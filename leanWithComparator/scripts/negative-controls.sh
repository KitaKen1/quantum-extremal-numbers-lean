#!/usr/bin/env bash
set -euo pipefail
QEX_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
test "$(uname -s)" = Linux
python3 "$QEX_ROOT/scripts/check-tools.py"
QEX_CONTROL="$QEX_ROOT/.lake/comparator-controls"
test ! -e "$QEX_CONTROL"
mkdir -p "$QEX_CONTROL" "$QEX_ROOT/evidence/controls"
python3 - "$QEX_ROOT" "$QEX_CONTROL" <<'PY'
from pathlib import Path
import json,sys
root,work=map(Path,sys.argv[1:])
(work/'lean-toolchain').write_bytes((root/'lean-toolchain').read_bytes())
modules={
    'Challenge':'theorem comparatorControl : (0 : Nat) = 0 := by sorry\n',
    'Good':'theorem comparatorControl : (0 : Nat) = 0 := by rfl\n',
    'WrongStatement':'theorem comparatorControl : (1 : Nat) = 1 := by rfl\n',
    'ForbiddenAxiom':'axiom unauthorized : (0 : Nat) = 0\ntheorem comparatorControl : (0 : Nat) = 0 := unauthorized\n',
    'SorrySolution':'theorem comparatorControl : (0 : Nat) = 0 := by sorry\n',
}
(work/'lakefile.toml').write_text('name = "qex_comparator_controls"\n'+''.join('\n[[lean_lib]]\nname = "'+name+'"\n' for name in modules))
(work/'lake-manifest.json').write_text(json.dumps({'version':'1.2.0','packagesDir':'.lake/packages',
    'packages':[],'name':'qex_comparator_controls','lakeDir':'.lake','fixedToolchain':False},indent=2)+'\n')
for name,code in modules.items():(work/(name+'.lean')).write_text(code)
for name in list(modules)[1:]:
    (work/(name+'.json')).write_text(json.dumps({'challenge_module':'Challenge','solution_module':name,
        'theorem_names':['comparatorControl'],'permitted_axioms':['propext','Quot.sound','Classical.choice'],
        'enable_nanoda':False},indent=2)+'\n')
PY
bash "$QEX_ROOT/scripts/sandbox-run.sh" "$QEX_CONTROL" Good.json "$QEX_ROOT/evidence/controls/Good.log"
grep -Fxq 'Your solution is okay!' "$QEX_ROOT/evidence/controls/Good.log"
for QEX_CASE in WrongStatement ForbiddenAxiom SorrySolution; do
  if bash "$QEX_ROOT/scripts/sandbox-run.sh" "$QEX_CONTROL" "$QEX_CASE.json" "$QEX_ROOT/evidence/controls/$QEX_CASE.log"; then
    echo "Comparator incorrectly accepted $QEX_CASE" >&2
    exit 1
  fi
done
grep -Fq 'theorem statement do not match' "$QEX_ROOT/evidence/controls/WrongStatement.log"
grep -Fq "Illegal axiom detected: 'unauthorized'" "$QEX_ROOT/evidence/controls/ForbiddenAxiom.log"
grep -Fq "Illegal axiom detected: 'sorryAx'" "$QEX_ROOT/evidence/controls/SorrySolution.log"
printf 'PASS\n' > "$QEX_ROOT/evidence/controls/status.txt"
echo 'PASS: correct proof accepted; wrong statement, extra axiom and sorry rejected'
