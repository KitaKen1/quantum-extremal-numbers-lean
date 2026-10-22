# Qex94: fixed-commit Comparator verification

This project checks the three proofs linked by Formal Conjectures PR #6836:

- `QuantumExtremalNumber.qex_nine`: `Qex 9 4 = answer(112)`.
- `QuantumExtremalNumber.qex_ten.variants.upper`: `Qex 10 5 ≤ 208`.
- `QuantumExtremalNumber.qex_eleven.variants.upper`: `Qex 11 5 ≤ 422`.

The proof dependency is pinned to `KitaKen1/quantum-extremal-numbers-lean`
commit `7d7e3afdadabdb2fa964cea99711d05fc5652022`, with Lean 4.33.1,
FC `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. No proof port is used.

`Challenge.lean` independently repeats the four definitions from the PR at
head `3ea4821704dfde365879d6a2d6f2f58e8f8d54e9`. The original PR file is
preserved in `sources/pr-statement.lean` and is never imported. The challenge
has `sorry` bodies by design; the solution imports the three original proof
modules, with the same qualified declaration names, and no challenge import.
The 10- and 11-qubit targets are the upper bounds described in the PR, not
solutions of the still-open exact-value questions.

## Reproduce on Linux

Use a fresh checkout with Git, Python 3.11+, Go, elan and `systemd-run`.
The verification commands run as an unprivileged user. On a GitHub-hosted
Ubuntu runner, the checked-in workflow installs the prerequisites.

```bash
cd leanWithComparator
lake exe cache get
python3 scripts/check-inputs.py --require-proof --receipt-dir evidence/inputs
export COMPARATOR_TOOLS=/absolute/path/to/a/fresh/tools-directory
bash scripts/install-tools.sh
bash scripts/negative-controls.sh
bash scripts/verify.sh
```

Do not prebuild Solution in the checking environment. Comparator first builds
and exports Challenge, then builds and exports Solution in Landrun and checks
the statement, transitive axiom dependencies and Lean kernel acceptance. The
driver additionally runs the axiom audit and `leanchecker --fresh Solution`
after Comparator succeeds. The success receipt is written only after all
checks, including input integrity checks before and after, succeed.

The tool commits and the **toolchain-only** change from 4.33.0 to 4.33.1 follow
the tested setup in [entropic-rogers-shephard](https://github.com/KitaKen1/entropic-rogers-shephard/tree/main/lean/comparator).
No Comparator/exporter Lean source is patched. The installer and driver verify
this. The three permitted axioms are `propext`, `Quot.sound`, and
`Classical.choice`; neither `sorryAx` nor project-specific axioms are permitted.
`enable_nanoda` is explicitly false because the pinned legacy CLI requires
that field. The separate fresh replay uses Lean's checker, not nanoda.

The negative controls must accept a correct proof and reject a changed
statement, an extra axiom and `sorry`, with the expected diagnostic.

## Public CI

The workflow [`.github/workflows/qex94-comparator.yml`](../.github/workflows/qex94-comparator.yml)
runs on `main` when verification inputs change and can also be started manually.
Logs and JSON receipts are uploaded on both success and failure. The full protocol
passed a private pilot on 2026-10-22; this public run uses the same verification
sources and pinned dependencies, with only the workflow trigger changed to `main`.
A completed public run and downloaded receipt hashes will be recorded in
[`../ComparatorLog20261022/`](../ComparatorLog20261022/).

This is an author-controlled CI reproduction; it is not a third-party review.
The proof dependency remains the original commit `7d7e3afdadabdb2fa964cea99711d05fc5652022`,
even though the verification kit is published later in this same repository.

On the private Ubuntu runner, Comparator including the proof build took 8 min
24 sec; the full-environment fresh replay took 32 min 23 sec. Allow sufficient
disk space and time when reproducing this complete protocol.

On macOS, the Lean project can be compiled and audited, but the Linux sandboxed
Comparator driver intentionally refuses to run. No unsandboxed shim is used.
