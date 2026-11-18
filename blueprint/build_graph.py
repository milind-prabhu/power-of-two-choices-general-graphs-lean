#!/usr/bin/env python3
"""Generate a self-contained PFR-style blueprint from compiled Lean dependencies.

Run from the project root after `lake env lean blueprint/Extract.lean`.
Graphviz is the only external rendering dependency. No browser/network is needed.
"""
from pathlib import Path
import argparse, collections, html, json, re, subprocess, textwrap

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
OUT = HERE / 'generated'
OUT.mkdir(exist_ok=True)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--overview-only', action='store_true', help='Rebuild the overview while retaining existing detailed views.')
args = parser.parse_args()
raw = {r['name']: r for r in json.loads((HERE/'compiled_dependencies.json').read_text())}
source = json.loads((HERE/'source_index.json').read_text())
records = {n: dict(raw[n], **source[n]) for n in source if n in raw}
raw_deps = {n: [d for d in r['used'] if d in raw and d != n] for n,r in raw.items()}

# Expository choices are separate from the compiled dependency evidence.
config = json.loads((HERE/'overview.json').read_text())
friendly = {n.removeprefix('GraphChoices.'): v['label'] for n,v in config.items()}
overview_names = list(config)
assert all(n in records for n in overview_names), set(overview_names)-records.keys()
assert source.keys() <= raw.keys(), 'Source declarations missing from compiled extraction'
mains = {'GraphChoices.mainTheorem', 'GraphChoices.LowerBound.greedyLowerBound'}

def displayed_dependencies(selected):
    """Nearest displayed dependencies, traversing omitted compiled helper constants."""
    selected = set(selected)
    edges, witnesses = set(), {}
    for target in sorted(selected):
        queue = collections.deque((d,[target,d]) for d in raw_deps.get(target,[]))
        seen = {target}
        while queue:
            dep,path = queue.popleft()
            if dep in seen: continue
            seen.add(dep)
            if dep in selected:
                edges.add((dep,target)); witnesses[(dep,target)] = list(reversed(path))
            else:
                queue.extend((d,path+[d]) for d in raw_deps.get(dep,[]) if d not in seen)
    return edges,witnesses

def reach(start,adj,skip=None):
    seen=set(); todo=[start]
    while todo:
        x=todo.pop()
        for y in adj.get(x,[]):
            if (x,y)==skip or y in seen: continue
            seen.add(y); todo.append(y)
    return seen

def reduce_edges(nodes,edges):
    """Remove redundant transitive arrows only for an acyclic displayed graph."""
    adj={n:[] for n in nodes}; indeg={n:0 for n in nodes}
    for a,b in edges: adj[a].append(b); indeg[b]+=1
    todo=[n for n in nodes if indeg[n]==0]; visited=0
    while todo:
        n=todo.pop(); visited+=1
        for b in adj[n]:
            indeg[b]-=1
            if not indeg[b]:todo.append(b)
    if visited!=len(nodes): return edges,False
    return {e for e in edges if e[1] not in reach(e[0],adj,skip=e)},True

node_ids={n:'decl_'+str(i) for i,n in enumerate(sorted(records))}
nodes={}
summaries = json.loads((HERE/'descriptions.json').read_text())
assert records.keys() <= summaries.keys(), 'Missing node descriptions'
for n,r in records.items():
    short=n.removeprefix('GraphChoices.')
    nodes[node_ids[n]]={
      'id':node_ids[n], 'name':n, 'label':friendly.get(short,short),
      'kind':'theorem' if raw[n]['kind']=='theorem' else 'definition',
      'summary':summaries[n],
      'statement':raw[n]['statement'], 'file':r['file'], 'line':r['line'],
      'source':r['source'], 'checked':True,
    }

def proof_ancestors(target):
    seen = set()
    todo = [target]
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        todo.extend(raw_deps.get(n, []))
    return sorted(seen & records.keys())

views={
 'overview':('Overview',overview_names),
 'upper':('Theorem 1.1 · Upper bound',proof_ancestors('GraphChoices.mainTheorem')),
 'lower':('Theorem 1.2 · Greedy lower bound',proof_ancestors('GraphChoices.LowerBound.greedyLowerBound')),
 'full':('All public declarations',sorted(records)),
}
graph_data=json.loads((OUT/'graph_data.json').read_text())['views'] if args.overview_only else {}
for key,(title,chosen) in views.items():
    if args.overview_only and key != 'overview': continue
    edges,paths=displayed_dependencies(chosen)
    edges,acyclic=reduce_edges(chosen,edges)
    edge_list=[{'from':node_ids[a],'to':node_ids[b],'path':paths[(a,b)]} for a,b in sorted(edges)]
    lines=['digraph proof {',
      'graph [rankdir=TB,bgcolor="white",pad="0.22",nodesep="0.24",ranksep="0.55",splines=polyline,outputorder=edgesfirst];',
      'node [fontname="DejaVu Sans",fontsize=10,style=filled,fillcolor="#b9e5b2",color="#23823c",fontcolor="#133b1e",penwidth=1.3,margin="0.13,0.08"];',
      'edge [color="#748076",arrowsize=0.65,penwidth=0.8];']
    for n in sorted(chosen):
        d=nodes[node_ids[n]]
        label=d['label'] if key=='overview' else n.removeprefix('GraphChoices.')
        label='\n'.join('\n'.join(textwrap.wrap(part,width=35,break_long_words=True,break_on_hyphens=False)) for part in label.split('\n'))
        attrs={'id':d['id'],'label':label,'shape':'ellipse' if d['kind']=='theorem' else 'box',
          'tooltip':n+' — Lean-checked'}
        if n in mains: attrs.update(penwidth='2.5',peripheries='2',fillcolor='#8fd18b',fontsize='12')
        lines.append(json.dumps(n)+' ['+','.join(k+'='+json.dumps(v,ensure_ascii=False) for k,v in attrs.items())+'];')
    for a,b in sorted(edges): lines.append(json.dumps(a)+' -> '+json.dumps(b)+';')
    lines.append('}')
    dot=OUT/(key+'.dot');dot.write_text('\n'.join(lines))
    svg=OUT/(key+'.svg')
    subprocess.run(['dot','-Tsvg',str(dot),'-o',str(svg)],check=True)
    graph_data[key]={'title':title,'nodes':[node_ids[n] for n in sorted(chosen)],'edges':edge_list,
      'acyclic':acyclic,'svg':re.sub(r'^.*?(?=<svg\s)','',svg.read_text(),flags=re.S)}

data={'nodes':nodes,'views':graph_data,'main':[node_ids[n] for n in sorted(mains)],
      'audit_count':(ROOT/'Audit.lean').read_text().count('#print axioms'),
      'extraction':'Lean 4.24.0 compiled ConstantInfo types and values; omitted helper constants traversed; transitive redundant arrows removed when acyclic.',
      'raw_declaration_count':len(raw),'source_declaration_count':len(records),
      'foundational_axioms':['propext','Classical.choice','Quot.sound'],
      'inspiration':'https://teorth.github.io/pfr/blueprint/dep_graph_document.html'}
(OUT/'graph_data.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
template=(HERE/'template.html').read_text()
payload=json.dumps(data,ensure_ascii=False).replace('</','<\\/')
(OUT/'Graph_Choices_Blueprint.html').write_text(template.replace('__GRAPH_DATA__',payload))
subprocess.run(['dot','-Tpdf',str(OUT/'overview.dot'),'-o',str(OUT/'Graph_Choices_Dependency_Graph.pdf')],check=True)
subprocess.run(['dot','-Tpng','-Gdpi=110',str(OUT/'overview.dot'),'-o',str(OUT/'Graph_Choices_Dependency_Graph.png')],check=True)
(OUT/'Graph_Choices_Dependency_Graph.svg').write_text((OUT/'overview.svg').read_text())
print(json.dumps({'source_nodes':len(records),'overview_nodes':len(overview_names),
 'views':{k:{'nodes':len(v['nodes']),'edges':len(v['edges']),'acyclic':v['acyclic']} for k,v in graph_data.items()}},indent=2))
