# Pull request draft

Before opening the pull request:

1. Push this repository to GitHub, then fill in the proof links of the statement file:
   `python3 lean/scripts/fill_links.py KitaKen1/<repo> <full-commit-sha>`.
   The script points the `formal_proof` link of `qex_nine` at its line in
   `lean/Qex94/Main.lean` and fills in the repository link of the reference [Kit26].
2. Copy `QuantumExtremalNumber.lean` to
   `FormalConjectures/Arxiv/2411.12208/QuantumExtremalNumber.lean` in a fork of Formal
   Conjectures, replace its first comment by the standard header of Formal Conjectures
   (`Copyright 2026 The Formal Conjectures Authors.` and the Apache License notice, which the
   copyright linter requires), and run
   `lake --wfail build 'FormalConjectures.Arxiv.«2411.12208».QuantumExtremalNumber'`.
   (Checked on commit `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` with placeholder links.)
3. Optionally open an issue first, as
   [CONTRIBUTING.md](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md)
   suggests.

---

**Title:** Add quantum extremal numbers (arXiv:2411.12208) and mark Qex(9) = 112 as solved

This PR adds the quantum extremal numbers of
[Zhang, Ning, Shi and Zhang, *Extremal Maximal Entanglement*](https://arxiv.org/abs/2411.12208)
(Phys. Rev. A 111, 052410, 2025). For a pure state $\psi$ of $n$ qubits, $m_k(\psi)$ is the
number of $k$-sets of qubits whose reduced density matrix is $I/2^k$, and
$\mathrm{Q}_{ex}(n,k)$ is the maximum of $m_k(\psi)$. The file asks to determine
$\mathrm{Q}_{ex}(n,k)$ in general, states the exact values of Table I of the paper and, for the
other $n$ of the table, asks to determine $\mathrm{Q}_{ex}(n)$, as the conclusion of the paper
does.

Definitions:

- A state is a vector of `EuclideanSpace ℂ (Fin n → Fin 2)`, normalized by `‖ψ‖ = 1`.
- `amplitudeMatrix A ψ` is the matrix `M` of the amplitudes of `ψ` whose rows are the
  configurations `a` on `A` and whose columns are the configurations `b` on the complement; its
  entry is the amplitude of the configuration that is `a` on `A` and `b` elsewhere.
- `reducedDensity A ψ = M Mᴴ` is the partial trace over the complement of `A`.
- `numMaximallyMixed k ψ` counts the `k`-sets `A` with `reducedDensity A ψ = (2 ^ k)⁻¹ • 1`.
- `Qex n k` is the supremum of `numMaximallyMixed k ψ` over normalized `ψ`. There are only
  `n.choose k` sets of `k` qubits, so the set is bounded and the supremum is a maximum.

Statements:

| Declaration | Statement | Category |
| --- | --- | --- |
| `qex` | `Qex = answer(sorry)` | open |
| `qex_four`, `qex_seven`, `qex_eight` | $\mathrm{Q}_{ex}(4)=4$, $\mathrm{Q}_{ex}(7)=32$, $\mathrm{Q}_{ex}(8)=56$ | solved |
| `qex_nine` | `Qex 9 4 = answer(112)` | solved, formal proof |
| `qex_ten`, `qex_eleven`, `qex_twelve` | `= answer(sorry)` | open |

The exact values for `n = 4, 7, 8` are those of Table I of the paper. The docstrings of
`qex_ten`, `qex_eleven` and `qex_twelve` give the known bounds: the lower bounds 200, 396 and 540
and the upper bound 792 from Table I, and the upper bounds 208 and 422 from [Kit26], which improve
the bounds 240 and 461 of the table.

Proofs: https://github.com/KitaKen1/REPO (fill in after pushing). The external project imports
Formal Conjectures at commit `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1`, copies the
definitions of this file verbatim (an audit script checks the copy character for character),
and proves `qex_nine` with this exact statement, as well as `Qex 10 5 ≤ 208` and
`Qex 11 5 ≤ 422`. `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

AI Usage Disclosure: This formalization, mathematical exploration, proof development, and
documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using
GPT-6 Astra, and Claude Code using Claude Opus 5.5.
