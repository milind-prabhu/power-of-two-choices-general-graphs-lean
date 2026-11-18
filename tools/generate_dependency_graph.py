#!/usr/bin/env python3
"""Rebuild the offline PFR-style file-import viewer. Requires Graphviz dot."""
from pathlib import Path
import re, json, html, subprocess, hashlib
from collections import deque

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'dependency-graph'
OUT.mkdir(exist_ok=True)
(OUT/'sources').mkdir(exist_ok=True)
files=sorted((ROOT/'GraphChoices').glob('*.lean'))
names={p.stem for p in files}
nodes=[]
for p in files:
    source=p.read_text(); ns=''; declarations=[]
    for number,line in enumerate(source.splitlines(),1):
        match=re.match(r'^namespace (\S+)',line)
        if match: ns=match.group(1)
        match=re.match(r'^\s*(?:(?:noncomputable|partial|private|protected)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class)\s+(\S+)',line)
        if match:
            declarations.append({'name':ns+'.'+match.group(2),'kind':match.group(1),'line':number})
    imports=re.findall(r'^import GraphChoices\.(\w+)\s*$',source,re.M)
    assert all(i in names for i in imports)
    doc=re.search(r'/[-]!([\s\S]*?)-/',source)
    summary=' '.join(doc.group(1).split()) if doc else ''
    nodes.append({'id':p.stem,'file':'GraphChoices/'+p.name,'imports':imports,
        'theorems':sum(d['kind'] in ('theorem','lemma') for d in declarations),
        'declarations':declarations,'summary':summary,'sha256':hashlib.sha256(source.encode()).hexdigest()})
    code='\n'.join(f'<span class="line" id="L{i}"><a class="num" href="#L{i}">{i:4}</a> {html.escape(line)}</span>' for i,line in enumerate(source.splitlines(),1))
    page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+html.escape(p.name)+'</title><style>body{margin:30px;background:#fafcfb;color:#142b22;font:14px/1.65 monospace}a{color:#176941}pre{white-space:pre;overflow:auto}.line{display:block}.line:target{background:#fff2b0}.num{color:#81968b;text-decoration:none}header{font:16px system-ui;position:sticky;top:0;background:#fafcfb;padding:12px 0}</style><header><a href="../index.html">← Dependency graph</a> · '+html.escape(p.name)+'</header><pre>'+code+'</pre></html>'
    (OUT/'sources'/f'{p.stem}.html').write_text(page)
by_id={n['id']:n for n in nodes}
anc={}
def ancestors(name,stack=()):
    if name in anc:return anc[name]
    assert name not in stack, 'Import cycle: '+str(stack+(name,))
    result=set()
    for dep in by_id[name]['imports']:
        result.add(dep);result.update(ancestors(dep,stack+(name,)))
    anc[name]=result;return result
for name in by_id:ancestors(name)
full=[(dep,n['id']) for n in nodes for dep in n['imports']]
reduced=[(a,b) for a,b in full if not any(a in anc[c] for c in by_id[b]['imports'] if c!=a)]
audit=ROOT/'axiom-audit.log'
verification=(ROOT/'verification.log').read_text()
count=sum(n['theorems'] for n in nodes)
assert f'PASS: {count} named proved results; no sorryAx or additional axioms.' in verification
assert len(re.findall(r'depends on axioms:|does not depend on any axioms',audit.read_text()))==count
payload={'basis':'Explicit local Lean file imports; not theorem proof references.',
 'status':'Every displayed module built; every named result passed the axiom audit.',
 'theoremCount':count,'moduleCount':len(nodes),'fullEdges':full,'reducedEdges':reduced,'nodes':nodes,
 'verificationSha256':hashlib.sha256(verification.encode()).hexdigest()}
(OUT/'dependencies.json').write_text(json.dumps(payload,indent=2)+'\n')

def render(edges,basename):
    dot=['digraph dependencies {','graph [rankdir=TB,bgcolor="transparent",pad="0.45",nodesep="0.26",ranksep="0.65",outputorder=edgesfirst];',
         'node [shape=box,style="rounded,filled",fillcolor="#c7f0c2",color="#23834e",fontname="Helvetica",fontsize=12,margin="0.15,0.09",penwidth=1.5];',
         'edge [color="#698478",arrowsize=0.55,penwidth=0.8];']
    for n in nodes:
        key=n['id']; goal=key in ('MainProof','GreedyLowerBound')
        attrs={'id':'node-'+key,'label':key+chr(10)+str(n['theorems'])+' checked result'+('s' if n['theorems']!=1 else ''),
               'tooltip':key+' — '+(n['summary'] or n['file'])}
        if goal:attrs.update(shape='ellipse',fillcolor='#1c8054',fontcolor='white',color='#105b3a',penwidth='2.8',peripheries='2')
        dot.append(json.dumps(key)+' ['+','.join(k+'='+json.dumps(v,ensure_ascii=False) for k,v in attrs.items())+'];')
    for a,b in edges:
        dot.append(json.dumps(a)+' -> '+json.dumps(b)+' [id='+json.dumps('edge-'+a+'--'+b)+'];')
    dot.append('}')
    path=OUT/(basename+'.dot');path.write_text('\n'.join(dot)+'\n')
    subprocess.run(['dot','-Tsvg',str(path),'-o',str(OUT/(basename+'.svg'))],check=True)
    svg=(OUT/(basename+'.svg')).read_text()
    return svg[svg.index('<svg'):]
svgs={'reduced':render(reduced,'dependencies'),'full':render(full,'dependencies-full')}
template=(ROOT/'tools/dependency_graph_template.html').read_text()
template=template.replace('__GRAPH_DATA__',json.dumps(payload).replace('</','<'+chr(92)+'/'))
template=template.replace('__REDUCED_SVG__',svgs['reduced']).replace('__FULL_SVG__',svgs['full'])
(OUT/'index.html').write_text(template)
print(json.dumps({'modules':len(nodes),'checkedResults':count,'imports':len(full),'reducedEdges':len(reduced),'viewer':str(OUT/'index.html')}))
