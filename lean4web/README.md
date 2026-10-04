# Complete proof in one file (Lean4Web version)

[`Qex94Lean4Web.lean`](Qex94Lean4Web.lean) proves the same theorems as [`../lean/`](../lean/)
in a single file that imports only Mathlib:

```lean
theorem QuantumExtremalNumber.qex_nine : Qex 9 4 = answer(112)
theorem QuantumExtremalNumber.qex_ten.variants.upper : Qex 10 5 ≤ 208
theorem QuantumExtremalNumber.qex_eleven.variants.upper : Qex 11 5 ≤ 422
```

It is generated from the modules of `../lean/Qex94/` by
[`../lean/scripts/make_lean4web.py`](../lean/scripts/make_lean4web.py): each module becomes a
`section`, and the definitions are the same. Formal Conjectures is not available in Lean4Web, so
the file drops the metadata attributes and supplies the surface syntax of `answer( )` with a
local macro (`answer(t)` elaborates to `t`, as in Formal Conjectures for an explicit answer).

## Verification

```bash
lake update
lake exe cache get
lake env lean Qex94Lean4Web.lean
```

The file was checked with Lean and Mathlib `v4.34.0` (this project) and `v4.35.0-rc3`, the
versions of Lean4Web's "Stable Release" and "Latest Mathlib" projects on 2026-10-03: no errors,
no warnings, about 25 s of CPU time on an Apple M4. It ends with `#print axioms` for the three
theorems, each reporting only

```text
[propext, Classical.choice, Quot.sound]
```

The `../lean/` project remains the authoritative check against the definitions of Formal
Conjectures.
