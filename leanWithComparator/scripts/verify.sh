#!/usr/bin/env bash
set -euo pipefail
QEX_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
test "$(uname -s)" = Linux
cd "$QEX_ROOT"
mkdir -p evidence
printf 'NOT_RUN\n' > evidence/status.txt
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > evidence/status.txt; fi' EXIT
python3 scripts/check-inputs.py --require-proof --receipt-dir evidence/before
python3 scripts/check-tools.py
test "$(cat evidence/controls/status.txt)" = PASS
{
  date -u +started_utc=%FT%TZ
  uname -a
  id
  lake env lean --version
  printf 'proof_commit=%s\n' "$(git -C .lake/packages/qex94 rev-parse HEAD)"
  printf 'run=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
} > evidence/environment.txt
# Comparator builds/exports the trusted Challenge before building the Solution.
bash scripts/sandbox-run.sh "$QEX_ROOT" comparator.json "$QEX_ROOT/evidence/comparator.log"
grep -Fxq 'Lean default kernel accepts the solution' evidence/comparator.log
grep -Fxq 'Your solution is okay!' evidence/comparator.log
python3 scripts/check-inputs.py --require-proof --receipt-dir evidence/after-comparator
# Inspect the original solution only after the sandboxed comparison passed.
lake env lean Audit.lean 2>&1 | tee evidence/axioms.log
python3 scripts/check-axioms.py evidence/axioms.log evidence/axioms.json
# Run the original project's 20-theorem audit in this locked dependency environment.
lake env lean .lake/packages/qex94/lean/Qex94/Audit.lean 2>&1 | tee evidence/original-audit.log
python3 scripts/check-axioms.py evidence/original-audit.log evidence/original-audit.json --original
lake env lean .lake/packages/qex94/FClikeLean/QuantumExtremalNumber.lean \
  2>&1 | tee evidence/original-fc-statement.log
# Fresh kernel replay is distinct from Comparator's selected-theorem replay.
/usr/bin/time -v lake env leanchecker --fresh Solution \
  > evidence/fresh-replay.log 2> evidence/fresh-replay-time.log
grep -q 'Exit status: 0' evidence/fresh-replay-time.log
python3 scripts/check-inputs.py --require-proof --receipt-dir evidence/after-replay
python3 - <<'PY'
from pathlib import Path
import datetime,hashlib,json
root=Path.cwd(); out=root/'evidence';pins=json.loads((root/'pins.json').read_text())
record={'status':'PASS','checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'proof_commit':pins['proof_commit'],'targets':pins['targets'],
    'comparator':True,'axiom_audit':True,'original_audit':True,'fresh_replay':True,
    'negative_controls':True,'independent_third_party_review':False,
    'receipt_sha256':{str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.rglob('*')) if p.is_file() and p.name not in ['status.txt','result.json']}}
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
PY
printf 'PASS\n' > evidence/status.txt
echo 'PASS: all three original proofs compared, axiom-audited and freshly replayed'
