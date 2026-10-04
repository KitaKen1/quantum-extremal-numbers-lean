# Complete Lean proof (Formal Conjectures version)

This is the main proof project. It requires
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` (2026-10-01) and therefore uses the same toolchain,
Lean `v4.33.1` with Mathlib `0df444a`. The module [`Qex94/Statement.lean`](Qex94/Statement.lean)
imports `FormalConjecturesUtil` and repeats verbatim the definitions of the Formal
Conjectures–style statement file
[`../FClikeLean/QuantumExtremalNumber.lean`](../FClikeLean/QuantumExtremalNumber.lean)
(`amplitudeMatrix`, `reducedDensity`, `numMaximallyMixed`, `Qex`). The library proves

```lean
theorem QuantumExtremalNumber.qex_nine : Qex 9 4 = answer(112)
theorem QuantumExtremalNumber.qex_ten.variants.upper : Qex 10 5 ≤ 208
theorem QuantumExtremalNumber.qex_eleven.variants.upper : Qex 11 5 ≤ 422
```

## Modules

| Module | Content |
|:--|:--|
| [`Statement`](Qex94/Statement.lean) | The definitions of the statement file, verbatim |
| [`Basic`](Qex94/Basic.lean) | The abbreviations `Config n`, `StateVector n`, the predicate `IsMaximallyMixedOn` and the entries `reducedDensity_apply` used in the proofs; `mix T x y` and the purity `purC ψ T` as a four-fold amplitude sum; `p(T) = p(Tᶜ)` |
| [`Link`](Qex94/Link.lean) | `purC ψ A = Tr (ρ_A ρ_A)` for `ρ_A = reducedDensity A ψ`; maximally mixed ⇒ purity `2^{-|A|}`; normalized ⇒ `purC ψ ∅ = 1` |
| [`Shadow`](Qex94/Shadow.lean) | Lemma 2 of the top-level README: shadow inequalities for any `E` and any subsystem, `p W ≤ 2 p (W ∪ {i})`, Möbius positivity, all from local kernels with integer Gram vectors |
| [`Abstract`](Qex94/Abstract.lean) | Nine qubits: a real function with the purity properties has at most 112 four-sets of value `1/16` (Theorem A) |
| [`Lower`](Qex94/Lower.lean) | The graph state `H?SvCz}` and its 112 maximally mixed four-qubit reductions |
| [`Main`](Qex94/Main.lean) | `qex_nine` |
| [`PurityFacts`](Qex94/PurityFacts.lean) | Corollary 3 and level sums, for any number of qubits |
| [`Abstract10`](Qex94/Abstract10.lean), [`SignSums`](Qex94/SignSums.lean), [`Main10`](Qex94/Main10.lean) | Theorem B and `qex_ten.variants.upper` |
| [`KK11`](Qex94/KK11.lean), [`Abstract11`](Qex94/Abstract11.lean), [`Main11`](Qex94/Main11.lean) | Theorem C and `qex_eleven.variants.upper` |
| [`Audit`](Qex94/Audit.lean) | `#print axioms` for the main theorems |

The three kernel computations (`decide +kernel`) are the cut criterion in `Lower` and the two
colex initial segments in `KK11`. There is no `native_decide`.

## Verification

```bash
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The script runs `lake --wfail build Qex94 Qex94.Audit`, checks that the main theorems depend only
on `propext`, `Classical.choice` and `Quot.sound`, compares `Qex94/Statement.lean` with the
statement file, and compiles the statement file. It writes [`evidence/build.log`](evidence/build.log)
and [`evidence/build_results.json`](evidence/build_results.json). A build of the 16 modules from
scratch takes about 3 minutes on an Apple M4 (about 70 s of CPU time), after
`lake exe cache get`.

## Scripts

- [`scripts/build_audit.py`](scripts/build_audit.py): the audit above.
- [`scripts/make_lean4web.py`](scripts/make_lean4web.py): regenerates
  `../lean4web/Qex94Lean4Web.lean` from the modules.
- [`scripts/fill_links.py`](scripts/fill_links.py): after pushing, fills the repository name and
  commit into the `formal_proof` links and the Lean4Web link.
