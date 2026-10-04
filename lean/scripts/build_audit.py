#!/usr/bin/env python3
"""Build and audit the proof of `Qex 9 4 = answer(112)`.

1. `lake --wfail build Qex94 Qex94.Audit` (the audit module prints the axioms).
2. Every audited theorem may use only `propext`, `Classical.choice`, `Quot.sound`.
3. The definitions in `Qex94/Statement.lean` must equal, character for character, the
   definitions in the Formal Conjectures statement file `FClikeLean/QuantumExtremalNumber.lean`.
4. The Formal Conjectures statement file itself must compile (`lake env lean`).
Results go to `evidence/build.log` and `evidence/build_results.json`.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
evidence = root / "evidence"
evidence.mkdir(exist_ok=True)
fc_file = root.parent / "FClikeLean" / "QuantumExtremalNumber.lean"
if not fc_file.exists():
    fc_file = root / "FClike" / "QuantumExtremalNumber.lean"

start = time.monotonic()
proc = subprocess.Popen(["lake", "--wfail", "build", "Qex94", "Qex94.Audit"], cwd=root,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
lines = []
with (evidence / "build.log").open("w") as log:
    for line in proc.stdout:
        lines.append(line)
        log.write(line)
        log.flush()
        print(line, end="", flush=True)
build_rc = proc.wait()
build_out = "".join(lines)
elapsed = time.monotonic() - start

axioms = {}
for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", build_out):
    axioms[name] = [v.strip() for v in values.split(",") if v.strip()]
allowed = {"propext", "Classical.choice", "Quot.sound"}
required = [
    "QuantumExtremalNumber.qex_nine",
    "QuantumExtremalNumber.numMaximallyMixed_le_112",
    "QuantumExtremalNumber.exists_state_112",
    "QuantumExtremalNumber.Abstract.abstract_bound",
    "QuantumExtremalNumber.shadow_nonneg",
    "QuantumExtremalNumber.pur_le_two_mul_pur_insert",
    "QuantumExtremalNumber.purC_of_isMaximallyMixedOn",
    "QuantumExtremalNumber.purC_empty_of_norm_eq_one",
    "QuantumExtremalNumber.qex_ten.variants.upper",
    "QuantumExtremalNumber.numMaximallyMixed_le_208",
    "QuantumExtremalNumber.Abstract10.abstract_bound_ten",
    "QuantumExtremalNumber.shadow_nonneg_set",
    "QuantumExtremalNumber.shadow_ten",
    "QuantumExtremalNumber.qex_eleven.variants.upper",
    "QuantumExtremalNumber.numMaximallyMixed_le_422",
    "QuantumExtremalNumber.Abstract11.abstract_bound_eleven",
    "QuantumExtremalNumber.KK11.forty_le_card_shadow",
    "QuantumExtremalNumber.subsystem_shadow_nonneg",
    "QuantumExtremalNumber.moebius_nonneg",
    "QuantumExtremalNumber.shadow_eleven",
]
axiom_ok = all(n in axioms and set(axioms[n]) <= allowed for n in required)


def definitions(path: Path) -> str:
    text = path.read_text()
    begin = text.index("/-- The amplitudes of a state $\\psi$ of `n` qubits")
    last = "{m | ∃ ψ : EuclideanSpace ℂ (Fin n → Fin 2), ‖ψ‖ = 1 ∧ numMaximallyMixed k ψ = m}"
    return text[begin:text.index(last) + len(last)]


defs_match = definitions(root / "Qex94" / "Statement.lean") == definitions(fc_file)

fc_proc = subprocess.run(["lake", "env", "lean", str(fc_file)], cwd=root, text=True,
                         capture_output=True)
fc_errors = [l for l in (fc_proc.stdout + fc_proc.stderr).splitlines() if ": error" in l]
fc_ok = fc_proc.returncode == 0 and not fc_errors

ok = build_rc == 0 and axiom_ok and defs_match and fc_ok
files = [*sorted((root / "Qex94").glob("*.lean")), root / "Qex94.lean", fc_file,
         root / "lakefile.toml", root / "lake-manifest.json", root / "lean-toolchain",
         *sorted((root / "scripts").glob("*.py"))]
manifest = json.loads((root / "lake-manifest.json").read_text())
revs = {p["name"]: p.get("rev") for p in manifest.get("packages", [])}
result = {
    "status": "PASS" if ok else "FAIL",
    "scope": "Qex(9,4) = 112, Qex(10,5) <= 208 and Qex(11,5) <= 422 for all normalized complex pure states, in the FC definitions",
    "formal_target_theorems": ["QuantumExtremalNumber.qex_nine : Qex 9 4 = answer(112)", "QuantumExtremalNumber.qex_ten.variants.upper : Qex 10 5 ≤ 208", "QuantumExtremalNumber.qex_eleven.variants.upper : Qex 11 5 ≤ 422"],
    "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "command": "lake --wfail build Qex94 Qex94.Audit",
    "exit_code": build_rc,
    "elapsed_seconds": round(elapsed, 3),
    "timing_note": "Lake may reuse compiled modules; elapsed time is not pure checking time.",
    "lean_version": (root / "lean-toolchain").read_text().strip(),
    "fc_commit": revs.get("formal_conjectures"),
    "mathlib_commit": revs.get("mathlib"),
    "axiom_audit_passed": axiom_ok,
    "axioms": axioms,
    "statement_definitions_match_fc_file": defs_match,
    "fc_statement_file_compiles": fc_ok,
    "source_sha256": {str(p.relative_to(root.parent) if p.is_relative_to(root.parent) else p):
                      hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
}
(evidence / "build_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ["status", "exit_code", "elapsed_seconds",
                                         "axiom_audit_passed",
                                         "statement_definitions_match_fc_file",
                                         "fc_statement_file_compiles"]}))
raise SystemExit(0 if ok else 1)
