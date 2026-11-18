#!/usr/bin/env python3
"""Validate the committed proof graph against its compiled dependency evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
raw = {r['name']: r for r in json.loads((HERE / 'compiled_dependencies.json').read_text())}
source = json.loads((HERE / 'source_index.json').read_text())
data = json.loads((HERE / 'generated/graph_data.json').read_text())
provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())

for file, expected in provenance['lean_sources_sha256'].items():
    assert hashlib.sha256((ROOT / file).read_bytes()).hexdigest() == expected, file
assert source.keys() <= raw.keys(), 'Source names missing from compiled environment'
assert {n['name'] for n in data['nodes'].values()} == set(source)
for node in data['nodes'].values():
    name = node['name']
    assert node['statement'] and node['statement'] == raw[name]['statement'], name
    assert node['summary'].strip(), name
    assert node['source'] == source[name]['source'], name
    assert (node['file'], node['line']) == (source[name]['file'], source[name]['line']), name
    lines = (ROOT / node['file']).read_text().splitlines()
    assert '\n'.join(lines[node['line'] - 1:]).lstrip().startswith(node['source']), name

audited = set(re.findall(r'^#print axioms (\S+)$', (ROOT / 'Audit.lean').read_text(), re.M))
theorems = {name for name in source if raw[name]['kind'] == 'theorem'}
assert theorems == audited and len(audited) == 578
assert len(data['views']['overview']['nodes']) == 12
assert set(data['main']) <= set(data['views']['overview']['nodes'])
count = 0
for key, view in data['views'].items():
    assert len(set(view['nodes'])) == len(view['nodes']), key
    for edge in view['edges']:
        assert edge['from'] in view['nodes'] and edge['to'] in view['nodes'], key
        path = edge['path']
        assert path[0] == data['nodes'][edge['from']]['name']
        assert path[-1] == data['nodes'][edge['to']]['name']
        assert all(a in raw[b]['used'] for a, b in zip(path, path[1:])), path
        count += 1
print(f'PASS: {len(source)} declarations, {count} witnessed arrows, {len(audited)} audited results; original Lean sources unchanged.')
