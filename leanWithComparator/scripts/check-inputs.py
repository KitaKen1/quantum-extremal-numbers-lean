#!/usr/bin/env python3
"""Check the independent specification, exact proof sources, dependencies and driver."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
args = argparse.ArgumentParser()
args.add_argument('--require-proof', action='store_true')
args.add_argument('--receipt-dir', type=Path)
opts = args.parse_args()
pins = json.loads((ROOT / 'pins.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

for name, expected in pins['files_sha256'].items():
    file = ROOT / name
    if not file.is_file() or sha(file) != expected:
        raise SystemExit('Input hash mismatch: ' + name)
config = json.loads((ROOT / 'comparator.json').read_text())
assert config['theorem_names'] == pins['targets']
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
assert config['enable_nanoda'] is False
assert config.get('definition_names', []) == []
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
assert (ROOT / 'lean-toolchain').read_text().strip() == pins['lean_toolchain']

def definitions(text):
    begin = text.index('/-- The amplitudes')
    last = '{m | ∃ ψ : EuclideanSpace ℂ (Fin n → Fin 2), ‖ψ‖ = 1 ∧ numMaximallyMixed k ψ = m}'
    return text[begin:text.index(last, begin) + len(last)]

challenge = (ROOT / 'Challenge.lean').read_text()
pr = (ROOT / 'sources/pr-statement.lean').read_text()
assert definitions(challenge) == definitions(pr), 'Challenge definitions differ from PR'
assert sha(ROOT / 'sources/pr-statement.lean') == pins['pr_statement_sha256']
for short, typ in pins['target_types'].items():
    match = re.findall(r'theorem\s+' + re.escape(short) + r'\s*:\s*(.*?)\s*:=\s*by', challenge, re.S)
    assert match == [typ], 'Challenge target differs: ' + short
assert not re.search(r'^import\s+Qex94', challenge, re.M)
assert not re.search(r'^import\s+Challenge', (ROOT / 'Solution.lean').read_text(), re.M)

manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
revs = {p['name']: p.get('rev') for p in manifest['packages']}
for package, expected in pins['dependency_commits'].items():
    assert revs.get(package) == expected, 'Dependency revision differs: ' + package
proof = ROOT / '.lake/packages/qex94'
proof_commit = None
if proof.is_dir():
    proof_commit = subprocess.check_output(['git', '-C', str(proof), 'rev-parse', 'HEAD'], text=True).strip()
    assert proof_commit == pins['proof_commit'], 'Proof checkout differs'
    assert not subprocess.check_output(['git', '-C', str(proof), 'diff', '--name-only', 'HEAD', '--', *pins['proof_files_sha256']], text=True).strip(), 'Proof sources modified'
    for name, expected in pins['proof_files_sha256'].items():
        assert sha(proof / name) == expected, 'Original proof source differs: ' + name
    assert definitions((proof / 'lean/Qex94/Statement.lean').read_text()) == definitions(pr)
elif opts.require_proof:
    raise SystemExit('Pinned proof checkout missing; fetch the committed dependencies first')

git = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True, capture_output=True)
record = {
    'status': 'PASS', 'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'checked_repository_commit': git.stdout.strip() if git.returncode == 0 else None,
    'proof_commit': proof_commit, 'pr_head': pins['pr_head'], 'targets': pins['targets'],
    'definitions_match_pr': True, 'dependency_commits': revs,
    'pins_sha256': sha(ROOT / 'pins.json'), 'files_sha256': pins['files_sha256'],
    'platform': platform.platform(), 'run': {k: os.environ.get(k) for k in
        ['GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']},
}
if opts.receipt_dir:
    opts.receipt_dir.mkdir(parents=True, exist_ok=True)
    (opts.receipt_dir / 'input-check.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: pinned inputs, PR definitions, target types and dependencies' + ('; original proof sources verified' if proof_commit else ''))
