#!/usr/bin/env python3
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
pins = json.loads((root / 'pins.json').read_text())
text = Path(sys.argv[1]).read_text()
records = {}
names = pins['targets']
if '--original' in sys.argv[3:]:
    audit = root / '.lake/packages/qex94/lean/Qex94/Audit.lean'
    names = re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M)
    assert len(names) == 20 and set(pins['targets']) <= set(names)
for name in names:
    matches = re.findall("'" + re.escape(name) + r"' depends on axioms: \[(.*?)\]", text, re.S)
    if len(matches) != 1:
        raise SystemExit('Missing or duplicate axiom result: ' + name)
    axioms = [x.strip() for x in matches[0].split(',') if x.strip()]
    if set(axioms) - {'propext', 'Quot.sound', 'Classical.choice'}:
        raise SystemExit('Forbidden axiom: ' + name)
    records[name] = axioms
if 'sorryAx' in text or 'error:' in text:
    raise SystemExit('Axiom audit failed')
Path(sys.argv[2]).write_text(json.dumps({'status': 'PASS', 'targets': records}, indent=2) + '\n')
print('PASS: all ' + str(len(names)) + ' audited theorems use only permitted axioms')
