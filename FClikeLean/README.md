# Statement file in the format of Formal Conjectures

This directory contains a statement file for the quantum extremal numbers of
[Zhang, Ning, Shi and Zhang](https://arxiv.org/abs/2411.12208), written in the format of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (like the files in
its `FormalConjectures/Arxiv/` folder). It is not part of Formal Conjectures and has not been
submitted there. At the pinned commit
[`df3f12d7`](https://github.com/google-deepmind/formal-conjectures/tree/df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1)
(2026-10-01), Formal Conjectures has no file for quantum extremal numbers, and no issue or pull
request mentions arXiv:2411.12208 (GitHub search, 2026-10-03).

## The file

[`QuantumExtremalNumber.lean`](QuantumExtremalNumber.lean) contains

- the definitions `amplitudeMatrix`, `reducedDensity`, `numMaximallyMixed` and `Qex`, where
  `Qex n k` is the largest number of maximally mixed `k`-qubit reductions of an `n`-qubit state
  of norm `1`;
- the general problem `qex` and one statement for each `n` in the status table of the
  top-level README:

  | Declaration | Statement | Case | Category |
  |:--|:--|:--|:--|
  | `qex` | `Qex = answer(sorry)` | all `n`, `k` | `research open` |
  | `qex_four` | `Qex 4 2 = 4` | `n = 4` (Higuchi–Sudbery 2000) | `research solved` |
  | `qex_seven` | `Qex 7 3 = 32` | `n = 7` (Huber–Gühne–Siewert 2017) | `research solved` |
  | `qex_eight` | `Qex 8 4 = 56` | `n = 8` (Zhang–Ning–Shi–Zhang 2025) | `research solved` |
  | `qex_nine` | `Qex 9 4 = answer(112)` | `n = 9` (this repository) | `research solved`, `formal_proof` |
  | `qex_ten` | `Qex 10 5 = answer(sorry)` | `n = 10`; docstring: `200 ≤ Qex(10) ≤ 208` | `research open` |
  | `qex_eleven` | `Qex 11 5 = answer(sorry)` | `n = 11`; docstring: `396 ≤ Qex(11) ≤ 422` | `research open` |
  | `qex_twelve` | `Qex 12 6 = answer(sorry)` | `n = 12`; docstring: `540 ≤ Qex(12) ≤ 792` | `research open` |

  The docstrings cite the lower bounds from Zhang–Ning–Shi–Zhang 2025 and the upper bounds 208
  and 422 from this repository ([Kit26]). The `formal_proof` link of `qex_nine` points to the
  theorem of the same name in [`../lean/Qex94/Main.lean`](../lean/Qex94/Main.lean); the upper
  bounds are proved in [`../lean/Qex94/Main10.lean`](../lean/Qex94/Main10.lean) and
  [`../lean/Qex94/Main11.lean`](../lean/Qex94/Main11.lean). Before publishing, the placeholders
  `REPO` and `COMMIT` are filled in by
  `python3 ../lean/scripts/fill_links.py KitaKen1/<repo> <commit>`.

As in Formal Conjectures, every research statement is closed `by sorry`, including `qex_nine`,
which has a `formal_proof` link; the proofs live in [`../lean/`](../lean/) and
[`../lean4web/`](../lean4web/).

## What was checked

With the file copied into a checkout of Formal Conjectures at `df3f12d7` as
`FormalConjectures/Arxiv/2411.12208/QuantumExtremalNumber.lean`,

```bash
lake exe cache get
lake build 'FormalConjectures.Arxiv.«2411.12208».QuantumExtremalNumber'
```

succeeds. Of the library's linters (module docstring, namespace, category, AMS, answer,
docstrings, `formal_proof`, copyright header), only the copyright-header check reports anything:
it expects "The Formal Conjectures Authors" as the owner, while this file names its author. As a
check that the linters run, deleting one docstring makes the category-docstring linter report as
well.

## Relationship to the buildable projects

- [`../lean/Qex94/Statement.lean`](../lean/Qex94/Statement.lean) repeats the definitions of
  this file verbatim; [`../lean/scripts/build_audit.py`](../lean/scripts/build_audit.py)
  compares the two copies character for character and also compiles this file.
- [`../lean/Qex94/Main.lean`](../lean/Qex94/Main.lean) proves `qex_nine` with exactly the
  statement of this file; [`Main10.lean`](../lean/Qex94/Main10.lean) and
  [`Main11.lean`](../lean/Qex94/Main11.lean) prove the upper bounds `Qex 10 5 ≤ 208` and
  `Qex 11 5 ≤ 422` that the docstrings of `qex_ten` and `qex_eleven` cite.
- [`PR_DRAFT.md`](PR_DRAFT.md) is a draft of the pull request to Formal Conjectures.
