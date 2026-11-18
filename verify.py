#!/usr/bin/env python3
"""Build every module, audit proof dependencies, and reject proof placeholders."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent
audit_text = (root / 'Audit.lean').read_text()
audited_names = set(re.findall(r'^#print axioms (\S+)$', audit_text, re.M))
for path in sorted((root / 'GraphChoices').glob('*.lean')):
    text = path.read_text()
    namespace = ''
    # This is an auxiliary lexical check. Lean's axiom audit below is definitive.
    for number, line in enumerate(text.splitlines(), 1):
        # Project modules use fully qualified namespace declarations. Compare
        # complete names: a conditional theorem must not mask an unconditional
        # theorem whose name is its prefix.
        ns = re.match(r'^namespace (\S+)', line)
        if ns:
            namespace = ns.group(1)
        declaration = re.match(r'^\s*(?:theorem|lemma)\s+(\S+)', line)
        if declaration:
            name = f'{namespace}.{declaration.group(1)}'
            if name not in audited_names:
                raise SystemExit(f'Proved result missing from axiom audit: {name}')
        if re.match(r'^\s*(?:sorry|admit|axiom|unsafe)\b', line):
            raise SystemExit(f'Forbidden declaration or proof placeholder: {path}:{number}')
subprocess.run(['lake', 'build'], cwd=root, check=True)
audit = subprocess.run(['lake', 'env', 'lean', 'Audit.lean'], cwd=root,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
(root / 'axiom-audit.log').write_text(audit.stdout)
if 'sorryAx' in audit.stdout:
    raise SystemExit('A proved result depends on sorryAx')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', audit.stdout):
    used = {name.strip() for name in group.split(',') if name.strip()}
    if used - allowed:
        raise SystemExit(f'Unexpected axiom dependencies: {sorted(used - allowed)}')
count = (root / 'Audit.lean').read_text().count('#print axioms ')
print(f'PASS: {count} named proved results; no sorryAx or additional axioms.')
