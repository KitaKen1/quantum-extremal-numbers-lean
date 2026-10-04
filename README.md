# A Lean proof that Qex(9) = 112, with new bounds for 10 and 11 qubits

The *quantum extremal number* asks how many reductions of one pure state can be maximally
mixed at the same time:

```text
Problem (quantum extremal numbers). For a pure state ψ of n qubits, let m_k(ψ) be the number of
k-element sets A of qubits whose reduced state is maximally mixed, ρ_A = I / 2^k. Determine

                     Qex(n, k) = max { m_k(ψ) : ψ a pure state of n qubits },

and in particular Qex(n) = Qex(n, ⌊n/2⌋).
```

The current values and bounds of `Qex(n)` are in the table below; the background on absolutely
maximally entangled (AME) states and earlier work is in the [appendix](#appendix-history-and-related-work).

**Status of Qex(n), October 2026:**

| n | binom(n, ⌊n/2⌋) | Known before this repository | Now |
|:--:|:--:|:--|:--|
| 2, 3, 5, 6 | 2, 3, 10, 20 | ✅ all (AME states exist) [Huber–Gühne–Siewert 2017] | ✅ all |
| 4 | 6 | ✅ 4 [Higuchi–Sudbery 2000] | ✅ 4 |
| 7 | 35 | ✅ 32 [Huber–Gühne–Siewert 2017] | ✅ 32 |
| 8 | 70 | ✅ 56 [ZNSZ 2025] | ✅ 56 |
| **9** | 126 | 112 ≤ Qex ≤ 120 [ZNSZ 2025; ZHZ 2026] | 🆕 **Qex = 112** 🔷 |
| **10** | 252 | 200 ≤ Qex ≤ 240 [ZNSZ 2025] | ❓ 200 ≤ Qex ≤ **208** 🆕🔷 |
| **11** | 462 | 396 ≤ Qex ≤ 461 [ZNSZ 2025] | ❓ 396 ≤ Qex ≤ **422** 🆕🔷 |
| 12 | 924 | 540 ≤ Qex ≤ 792 [ZNSZ 2025] | ❓ 540 ≤ Qex ≤ 792 |

✅ known before this repository (attributions as in [ZNSZ 2025, Table I]) · 🆕 first proved in
this repository, to our knowledge (see [status boundary](#status-boundary)) · 🔷 proved in Lean
in this repository · ❓ open

**This repository contributes the following** (every proof is complete and checked by the Lean
kernel, Lean 4 with Mathlib):

1. **A statement file in the format of Formal Conjectures.**
   [`FClikeLean/QuantumExtremalNumber.lean`](FClikeLean/QuantumExtremalNumber.lean) defines
   `Qex n k` and states the general problem, the known values and the open cases. Formal
   Conjectures does not contain quantum extremal numbers yet
   ([details](#formal-conjectures-target)).
2. **Qex(9) = 112.** Every pure state of 9 qubits has at most 112 maximally mixed 4-qubit
   reductions (new to our knowledge; the previous bound was 120), and the graph state of the
   9-vertex graph `H?SvCz}` has exactly 112 (this lower bound was known [ZNSZ 2025]).
3. **Qex(10) ≤ 208.** Every pure state of 10 qubits has at most 208 maximally mixed 5-qubit
   reductions (previously 240).
4. **Qex(11) ≤ 422.** Every pure state of 11 qubits has at most 422 maximally mixed 5-qubit
   reductions (previously 461).

The theorems cover every complex pure state. There is no stabilizer, graph-state or uniformity
assumption; the uniformity needed in the proof is derived. For 10 and 11 qubits these are upper
bounds only, and the exact values remain open.

**Try it in Lean4Web:**
[open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fquantum-extremal-numbers-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FQex94Lean4Web.lean)
(Lean4Web's default "Latest Mathlib" project; the file also checks on "Stable Release").

## Formal Conjectures target

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) does not yet contain
quantum extremal numbers (checked at commit
[`df3f12d7`](https://github.com/google-deepmind/formal-conjectures/tree/df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1),
2026-10-01). The folder [`FClikeLean/`](FClikeLean/) contains a statement file for it,
`QuantumExtremalNumber.lean`, written in the format of Formal Conjectures
(for `FormalConjectures/Arxiv/2411.12208/`). It defines `Qex n k`, asks to determine `Qex` in
general (`research open`), states the exact values `Qex(4)`, `Qex(7)`, `Qex(8)` and `Qex(9)` as
`research solved`, and asks for `Qex(10)`, `Qex(11)`, `Qex(12)` as `research open`, with their
known bounds in the docstrings.

The project [`lean/`](lean/) imports `FormalConjecturesUtil` (Formal Conjectures pinned to
`df3f12d7`), copies the definitions of the statement file verbatim into
[`lean/Qex94/Statement.lean`](lean/Qex94/Statement.lean) (the audit script checks the copy
character for character), and proves `qex_nine` with exactly the statement of the file, together
with the upper bounds for 10 and 11 qubits that the docstrings of `qex_ten` and `qex_eleven` cite:

```lean
theorem QuantumExtremalNumber.qex_nine : Qex 9 4 = answer(112)
theorem QuantumExtremalNumber.qex_ten.variants.upper : Qex 10 5 ≤ 208
theorem QuantumExtremalNumber.qex_eleven.variants.upper : Qex 11 5 ≤ 422
```

where

```lean
noncomputable def amplitudeMatrix {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∉ A} → Fin 2) ℂ :=
  fun a b => ψ (fun i => if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, h⟩)
noncomputable def reducedDensity {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∈ A} → Fin 2) ℂ :=
  amplitudeMatrix A ψ * (amplitudeMatrix A ψ)ᴴ
noncomputable def numMaximallyMixed {n : ℕ} (k : ℕ) (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) : ℕ :=
  (Finset.univ.filter fun A : Finset (Fin n) =>
    A.card = k ∧ reducedDensity A ψ = ((2 : ℂ) ^ k)⁻¹ • 1).card
noncomputable def Qex (n k : ℕ) : ℕ :=
  sSup {m | ∃ ψ : EuclideanSpace ℂ (Fin n → Fin 2), ‖ψ‖ = 1 ∧ numMaximallyMixed k ψ = m}
```

so a state is the vector of its `2^n` amplitudes, `amplitudeMatrix A ψ` arranges them as a matrix
`M` whose rows are the configurations `a` on `A` and whose columns are the configurations `b`
outside `A`, `reducedDensity A ψ = M Mᴴ` is the partial trace
`ρ_A(a, a') = Σ_b ψ(a, b) conj(ψ(a', b))` over the qubits outside `A`, and `Qex 9 4 = 112` says
exactly that the maximum number of maximally mixed four-qubit reductions of a normalized
nine-qubit state is 112.

## Mathematical explanation (AI generated)

This is a sketch of the mathematics that the Lean proof formalizes.

**Setting.** Fix a pure state $\psi$ of $n$ qubits. For a set $T$ of qubits let
$p(T)=\mathrm{Tr}\,\rho_T^2$ be the purity of its reduced state, and let
$P_k=\sum_{|T|=k}p(T)$. Call a $k$-set *good* if $p(T)=2^{-k}$ and *bad* otherwise. A maximally
mixed reduction is good, so it suffices to show that there are many bad sets. The whole argument
uses only the following properties of $p$.

**Lemma 1 (purities).** (a) $p(\emptyset)=1$. (b) $p(T)=p(T^c)$. (c) If $\rho_A=I/2^{|A|}$, then
$p(A)=2^{-|A|}$.

*Proof.* Write $x\triangleleft_T y$ for the configuration that agrees with $y$ on $T$ and with
$x$ off $T$. Then
$p(T)=\sum_{x,y}\psi(x)\psi(y)\overline{\psi(x\triangleleft_T y)}\,\overline{\psi(y\triangleleft_T x)}$,
so (a) is $\lVert\psi\rVert^4=1$, (b) follows from $x\triangleleft_{T^c}y=y\triangleleft_T x$, and (c) is
$p(A)=\sum_{a,a'}|\rho_A(a,a')|^2$ for $\rho_A=I/2^{|A|}$. $\square$

**Lemma 2 (two-copy positivity).** For sets $E\subseteq S$, a set $W$, a qubit $i\notin W$ and
a set $R$:

- (a) $\sum_{T\subseteq S}(-1)^{|T\setminus E|}\,p(T)\ge 0$ (the shadow inequalities of the
  reduced state on $S$);
- (b) $p(W)\le 2\,p(W\cup\lbrace i\rbrace)$;
- (c) $\sum_{U\subseteq R}(-1)^{|R\setminus U|}\,2^{|U|}\,p(U)\ge 0$.

*Proof.* Each left-hand side is a quadratic form in two copies of the state ($\psi\otimes\psi$
for (a), $\psi\otimes\bar\psi$ for (b) and (c)) whose kernel is a product, over the qubits, of
$4\times 4$ matrices on the pair of local labels: $1\pm\mathrm{SWAP}$ and $1$ for (a);
$1$, $2\cdot 1-ee^{\mathsf T}$ and $ee^{\mathsf T}$ (with $e=|00\rangle+|11\rangle$) for (b)
and (c). Each local matrix has an explicit integer Gram decomposition, for example
$1-\mathrm{SWAP}=(|01\rangle-|10\rangle)(\langle 01|-\langle 10|)$ and
$2\cdot 1-ee^{\mathsf T}=(|00\rangle-|11\rangle)(\langle 00|-\langle 11|)+2|01\rangle\langle 01|+2|10\rangle\langle 10|$,
so the form is a sum of squares. Expanding the product over the qubits gives the stated
combinations of purities. $\square$

For $S$ all qubits, (a) is Rains' shadow inequality [Rains 1999]. Inequality (b) is
$\lVert\mathrm{Tr}_i X\rVert_F^2\le 2\lVert X\rVert_F^2$ for $X=\rho_{W\cup\lbrace i\rbrace}$,
and the sum in (c) is $2^{|R|}$ times the squared weight of the Pauli strings with support exactly
$R$.

**Corollary 3.** (a) $p(T\cup\lbrace i\rbrace)\le 2\,p(T)$ for $i\notin T$ (apply Lemma 2(b) to
complements). (b) $p(T)\ge 2^{-|T|}$. (c) If $p(S)=2^{-|S|}$, then $p(U)=2^{-|U|}$ for every
$U\subseteq S$. In particular, if every set of at most two qubits lies in a good set, then
$p(U)=2^{-|U|}$ for $|U|\le 2$; this happens whenever the bad sets are few, since a pair lies in
many $k$-sets.

**Theorem A ($n=9$).** Every pure state of nine qubits has at least 14 bad four-sets.

*Proof.* Suppose there are at most 13. A pair of qubits lies in 21 four-sets, so $p(U)=2^{-|U|}$
for $|U|\le 2$. Summing Lemma 2(a) over $E=\lbrace i\rbrace$, $S$ all qubits, gives
$\sum_T(-1)^{|T|}(9-2|T|)\,p(T)\ge 0$; with $P_k=P_{9-k}$ (Lemma 1(b)) this reads
$45-6P_3+2P_4\ge 0$. For a four-set $S$ put
$a(S)=16\,p(S)-8\sum_{T\subset S,|T|=3}p(T)+3$. Then
$\sum_{|S|=4}a(S)=16P_4-48P_3+378=8(45-6P_3+2P_4)+18\ge 18$. On the other hand:

- $a(S)=0$ if $S$ is good (Corollary 3(c));
- $a(S)\le 3$ always (Corollary 3(a) for the four triples of $S$);
- $a(S)\le 1$ if a good four-set is disjoint from $S$ (then $p(S)=p(S^c)\le 2/16$).

Join two bad four-sets when they are disjoint. This graph is an induced subgraph of the Kneser
graph $KG(9,4)$: its degrees are at most 5, and it has no triangle and no 4-cycle. A vertex of
degree less than 5 has a good four-set in its complement, and three vertices of degree 5 would
force at least 14 vertices. So $\sum a\le 13+2\cdot 2=17<18$, a contradiction. $\square$

**Lower bound.** Let $|G\rangle=2^{-9/2}\sum_x(-1)^{q(x)}|x\rangle$ with
$q(x)=\sum_{ij\in E}x_ix_j$ for the graph `H?SvCz}` (line 435 of Danielsen's database of
nine-vertex graphs [Danielsen–Parker 2006]) with edges
`17 18 19 25 27 29 36 37 39 45 46 48 49 58 59 68 69 79`. A four-set $A$ has $\rho_A=I/16$
whenever every nonempty $D\subseteq A$ has a vertex outside $A$ with an odd number of neighbours in
$D$: for $a\ne a'$, take such a vertex for $D=\lbrace j:a_j\ne a'_j\rbrace$; flipping its bit in the
environment reverses the sign of every term of $\sum_b\psi(a,b)\overline{\psi(a',b)}$, so the sum
is 0. This criterion holds for exactly 112 of the 126 four-sets. (In Lean the state is multiplied
by the global phase $(1+i)/\sqrt 2$, so that every amplitude is $\pm(1+i)/32$ and no square root
appears.)

**Theorem B ($n=10$).** Every pure state of ten qubits has at least 44 bad five-sets.

*Proof.* Suppose there are at most 43. A pair lies in 56 five-sets, so $p(U)=2^{-|U|}$ for
$|U|\le 2$. Six copies of Lemma 2(a) for $E=\emptyset$ plus the inequalities for
$E=\lbrace i,j\rbrace$ over all ordered pairs $i\ne j$ (using
$\sum_{i\ne j}\varepsilon_i\varepsilon_j=s^2-n$) give
$\sum_T(-1)^{|T|}(|T|-4)(|T|-6)\,p(T)\ge 0$; the coefficients vanish at $|T|=4,6$. With
$P_k=P_{10-k}$ this is $78-6P_3+P_5\ge 0$, and $P_3\ge 120/8$ gives $P_5\ge 12$. Every five-set
$S$ contains a good four-set: otherwise the 25 sets $(S\setminus\lbrace i\rbrace)\cup\lbrace x\rbrace$
and their 25 complements would all be bad. So each bad five-set has $p\le 2/16$, and
$32P_5\le \#\text{good}+4\cdot\#\text{bad}\le 252+3\cdot 43<384$, a contradiction. $\square$

**Theorem C ($n=11$).** Every pure state of eleven qubits has at least 40 bad five-sets.

*Proof.* Suppose there are at most 39; again $p(U)=2^{-|U|}$ for $|U|\le 2$. Summing Lemma 2(a)
over all ordered triples of distinct qubits as $E$ (using
$\sum_{i,j,k\text{ distinct}}\varepsilon_i\varepsilon_j\varepsilon_k=s^3-3ns+2s$ for signs
$\varepsilon=\pm1$ with sum $s$) and folding with $P_k=P_{11-k}$ gives
$82.5+10P_3-22P_4+10P_5\ge 0$. Put
$D=\sum_{|S|=5}(32\,p(S)-1)$, $u=8P_3-165\ge 0$, and $t=16P_4-64P_3+990\ge 0$ (the sum of the
Möbius coefficients of the four-sets, Lemma 2(c)). Then $D\ge 66+(156u+22t)/5$. For a bad
five-set $S$, its share $32\,p(S)-1$ of $D$ is

- at most 1 if a good five-set lies in $S^c$;
- at most 3 if $S$ has a good four-subset;
- at most $1+2t$ in any case (Lemma 2(a) for the subsystem $S$, and Lemma 2(c)).

Call $S$ *high* if all six five-subsets of $S^c$ are bad. The six-sets $S^c$ of the high sets then
have all their five-subsets bad, and by the Kruskal–Katona theorem any 14 six-sets have at least
40 five-subsets; so there are at most 13 high sets. At most one bad five-set has no good
four-subset, since two such sets would force 49 bad five-sets. Hence
$D\le 39+2\cdot 13+2t=65+2t<66+22t/5$, a contradiction. $\square$

**In Lean.** The purity is defined as the four-fold amplitude sum of Lemma 1, and Lemma 2 is
proved once for products of local kernels with integer Gram vectors, so no Pauli matrices, no
square roots and no spectral theorem are needed. Each combinatorial core is a theorem about a
real function `p : Finset (Fin n) → ℝ` with the properties above
([`Abstract.lean`](lean/Qex94/Abstract.lean), [`Abstract10.lean`](lean/Qex94/Abstract10.lean),
[`Abstract11.lean`](lean/Qex94/Abstract11.lean)). Kruskal–Katona is Mathlib's
`Finset.kruskal_katona`. Only three steps are computations, all checked by the kernel with
`decide +kernel` (no `native_decide`): the cut criterion for the 126 four-sets (about 2.5 s), and
the sizes 14 and 40 of two initial segments of the colex order (about 2.5 s each). The proof
does not use the covering lemma of [ZNSZ 2025] or any classification of stabilizer states.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| [`lean/`](lean/) | `v4.33.1` | Complete proof. Lake project requiring Formal Conjectures at commit `df3f12d7` |
| [`lean4web/`](lean4web/) | `v4.34.0`, `v4.35.0-rc3` | Complete proof in a single Mathlib-only file for Lean4Web |
| [`FClikeLean/`](FClikeLean/) | — | Statement file in the format of Formal Conjectures, and a pull request draft |

`lean/` consists of the `Qex94` library: 16 modules, about 3,100 lines. The main theorems are in
[`Main.lean`](lean/Qex94/Main.lean) (nine qubits), [`Main10.lean`](lean/Qex94/Main10.lean) and
[`Main11.lean`](lean/Qex94/Main11.lean); see [`lean/README.md`](lean/README.md) for the modules.
The Lean4Web edition `lean4web/Qex94Lean4Web.lean` (about 3,100 lines) is generated from `lean/`
by [`make_lean4web.py`](lean/scripts/make_lean4web.py) and contains the same proofs.

## Verification

Formal Conjectures version (complete proof):

```bash
cd lean
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The audit runs `lake --wfail build Qex94 Qex94.Audit`, checks the axioms of the main theorems,
compares the definitions with the Formal Conjectures statement file and compiles that file. A
build of the 16 modules from scratch takes about 3 minutes on an Apple M4 (about 70 s of CPU
time); most of it is loading Mathlib, which needs up to about 7 GB of memory per Lean process.
The result is recorded in [`lean/evidence/build_results.json`](lean/evidence/build_results.json).

Standalone Mathlib/Lean4Web version (complete proof in one file):

```bash
cd lean4web
lake update
lake exe cache get
lake env lean Qex94Lean4Web.lean
```

This takes about 25 s of CPU time (Apple M4).

All results are kernel checked. The proof files contain no `sorry`, `admit`, custom axiom or
`native_decide`. The `#print axioms` commands for the main theorems report only Lean's standard
axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is proved here, for all complex pure states:

```text
Qex(9) = 112;    Qex(10) ≤ 208;    Qex(11) ≤ 422.
```

What remains open:

```text
200 ≤ Qex(10) ≤ 208;   396 ≤ Qex(11) ≤ 422;   540 ≤ Qex(12) ≤ 792;   Qex(n) for n ≥ 13.
```

To our knowledge the upper bounds 112, 208 and 422 had not been proved before: [ZNSZ 2025, Table I]
lists the upper bounds 120, 240 and 461, and the 2026 follow-up [ZHZ 2026] proves
$Q^{D}_{\mathrm{ex},\varepsilon}(9,4)\le 120$ for $0\le\varepsilon<1/17$. Our search beyond these
two papers was limited to targeted keyword searches. The lower bound 112 is not new: it is the
graph state from Danielsen's database to which [ZNSZ 2025] attributes the bound.

## Sources

- [ZNSZ 2025] W. Zhang, Y. Ning, F. Shi and X. Zhang, *Extremal Maximal Entanglement*,
  Phys. Rev. A 111, 052410 (2025). [arXiv:2411.12208](https://arxiv.org/abs/2411.12208)
- [ZHZ 2026] W. Zhang, Z. Han and X. Zhang, *Robust Quantum Extremal Numbers*, preprint (2026).
  [arXiv:2608.13907](https://arxiv.org/abs/2608.13907)
- [Higuchi–Sudbery 2000] A. Higuchi and A. Sudbery, *How entangled can two couples get?*,
  Phys. Lett. A 273, 213–217 (2000). [arXiv:quant-ph/0005013](https://arxiv.org/abs/quant-ph/0005013)
- [Huber–Gühne–Siewert 2017] F. Huber, O. Gühne and J. Siewert, *Absolutely maximally entangled
  states of seven qubits do not exist*, Phys. Rev. Lett. 118, 200502 (2017).
  [arXiv:1608.06228](https://arxiv.org/abs/1608.06228)
- [Scott 2004] A. J. Scott, *Multipartite entanglement, quantum-error-correcting codes, and
  entangling power of quantum evolutions*, Phys. Rev. A 69, 052330 (2004).
  [arXiv:quant-ph/0310137](https://arxiv.org/abs/quant-ph/0310137)
- [Facchi et al. 2008] P. Facchi, G. Florio, G. Parisi and S. Pascazio, *Maximally multipartite
  entangled states*, Phys. Rev. A 77, 060304 (2008). [arXiv:0710.2868](https://arxiv.org/abs/0710.2868)
- [Zha et al. 2019] X. Zha, I. Ahmed, D. Zhang and Y. Zhang, *A criterion to identify maximally
  entangled nine-qubit state*, preprint (2019). [arXiv:1907.05612](https://arxiv.org/abs/1907.05612)
- [Rains 1999] E. M. Rains, *Quantum shadow enumerators*, IEEE Trans. Inf. Theory 45, 2361–2366
  (1999). [arXiv:quant-ph/9611001](https://arxiv.org/abs/quant-ph/9611001)
- [Danielsen–Parker 2006] L. E. Danielsen and M. G. Parker, *On the classification of all
  self-dual additive codes over GF(4) of length up to 12*, J. Combin. Theory Ser. A 113,
  1351–1367 (2006). [arXiv:math/0504522](https://arxiv.org/abs/math/0504522);
  [database of graphs](https://www.codetables.de/larsed/vncorbits/)
- [Kruskal 1963] J. B. Kruskal, *The number of simplices in a complex*, in Mathematical
  Optimization Techniques, University of California Press (1963), 251–278.
- [Katona 1968] G. O. H. Katona, *A theorem of finite sets*, in Theory of Graphs (Tihany, 1966),
  Academic Press (1968), 187–207.
- The Kruskal–Katona theorem in Mathlib: `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`.
- [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), in particular
  `FormalConjectures/OpenQuantumProblems/35.lean` (existence of AME states).

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code
using Claude Opus 5.5.

## Appendix: history and related work

A pure state of `n` parties is *`k`-uniform* if all its `k`-party reductions are maximally mixed,
and *absolutely maximally entangled* if it is `⌊n/2⌋`-uniform. Scott [Scott 2004] introduced
`k`-uniform states and showed that an `n`-qubit state is `k`-uniform exactly when it is a pure
quantum error-correcting code `((n, 1, k + 1))`. Bounds on quantum codes, in particular Rains'
shadow bounds [Rains 1999], therefore limit AME states: for qubits they can exist only for
`n = 2, 3, 5, 6` and possibly `7`, and the case `n = 7` was ruled out by Huber, Gühne and Siewert
[Huber–Gühne–Siewert 2017]. When no AME state exists, one can ask how many of the
`binom(n, ⌊n/2⌋)` reductions can still be maximally mixed. This is `Qex(n)` [ZNSZ 2025]. A
related measure is the average purity of the balanced reductions, which is minimal exactly for
AME states [Scott 2004; Facchi et al. 2008].

### Timeline

| Year | Result |
|---|---|
| 1999 | Rains: quantum shadow enumerators; the shadow inequalities bound quantum codes. |
| 2000 | Higuchi–Sudbery: no four-qubit state has all six two-qubit reductions maximally mixed. |
| 2004 | Scott: `k`-uniform states are the pure `((n, 1, k + 1))` codes; by Rains' bounds, qubit AME states can exist only for `n = 2, 3, 5, 6, 7`. |
| 2006 | Danielsen–Parker: all self-dual additive codes over GF(4), equivalently graph states up to local Clifford equivalence, classified up to length 12; database of representative graphs. |
| 2008 | Facchi–Florio–Parisi–Pascazio: maximally multipartite entangled states, whose bipartite entanglement is maximal for every bipartition. |
| 2017 | Huber–Gühne–Siewert: no AME state of seven qubits, and an upper bound on the number of maximally mixed three-qubit reductions; `Qex(7) = 32` [ZNSZ 2025, Table I]. |
| 2019 | Zha–Ahmed–Zhang–Zhang: for nine-qubit states whose one-, two- and three-qubit reductions are maximally mixed, the average purity of the four-qubit reductions should be at least `1/14`, attained with purities `1/16`, `1/8` and `1/4`. |
| 2024 | Zhang–Ning–Shi–Zhang (Phys. Rev. A 2025): the name `Qex(n)`; a general upper bound via Turán's problem; lower bounds from graph states and a probabilistic argument; `Qex(8) = 56`; Table I with the values and bounds for `n ≤ 12`. |
| 2026 | Zhang–Han–Zhang (preprint): robust quantum extremal numbers; for nine qubits the bound `120` also holds for approximately maximally mixed reductions (`ε < 1/17`). |
| 2026 | This repository: `Qex(9) = 112`, `Qex(10) ≤ 208`, `Qex(11) ≤ 422`, with Lean proofs. |

### Status of Qex(n), October 2026

The table at the top of this README summarizes the status; it is repeated here, followed by the
details.

| n | binom(n, ⌊n/2⌋) | Known before this repository | Now |
|:--:|:--:|:--|:--|
| 2, 3, 5, 6 | 2, 3, 10, 20 | ✅ all (AME states exist) | ✅ all |
| 4 | 6 | ✅ 4 [Higuchi–Sudbery 2000] | ✅ 4 |
| 7 | 35 | ✅ 32 [Huber–Gühne–Siewert 2017] | ✅ 32 |
| 8 | 70 | ✅ 56 [ZNSZ 2025] | ✅ 56 |
| **9** | 126 | 112 ≤ Qex ≤ 120 [ZNSZ 2025; ZHZ 2026] | 🆕 **Qex = 112** 🔷 |
| **10** | 252 | 200 ≤ Qex ≤ 240 [ZNSZ 2025] | ❓ 200 ≤ Qex ≤ **208** 🆕🔷 |
| **11** | 462 | 396 ≤ Qex ≤ 461 [ZNSZ 2025] | ❓ 396 ≤ Qex ≤ **422** 🆕🔷 |
| 12 | 924 | 540 ≤ Qex ≤ 792 [ZNSZ 2025] | ❓ 540 ≤ Qex ≤ 792 |

✅ known before this repository · 🆕 first proved in this repository, to our knowledge · 🔷 proved
in Lean in this repository · ❓ open

**Who determined which values** (attributions as in [ZNSZ 2025, Table I])

| n | Qex(n) | Determined by |
|:--|:--|:--|
| 2, 3, 5, 6 | `binom(n, ⌊n/2⌋)` | existence of AME states (see [Huber–Gühne–Siewert 2017]) |
| 4 | 4 | Higuchi–Sudbery (2000) |
| 7 | 32 | Huber–Gühne–Siewert (2017) |
| 8 | 56 | Zhang–Ning–Shi–Zhang (2024/2025) |
| 9 | 112 | lower bound: a graph state from Danielsen's database, cited in [ZNSZ 2025]; upper bound: this repository |

**Best known bounds in the open cases**

| n | Lower bound | Upper bound |
|:--|:--|:--|
| 10 | 200, graph states [ZNSZ 2025] | 208, this repository (240 in [ZNSZ 2025]) |
| 11 | 396, graph states [ZNSZ 2025] | 422, this repository (461 in [ZNSZ 2025]) |
| 12 | 540, a circulant graph state [ZNSZ 2025] | 792 [ZNSZ 2025] |

### Related methods

- **Shadow inequalities.** Lemma 2(a) with `S` all qubits is Rains' shadow inequality
  [Rains 1999]; Scott [Scott 2004] relates the purities of the reductions to the weight
  enumerators of quantum codes. Here the purities are the only quantities used, and all
  positivity statements are proved from explicit sums of squares.
- **The bound `A₄ ≥ 18`.** For nine qubits with maximally mixed one-, two- and three-qubit
  reductions, an average four-qubit purity of at least `1/14` [Zha et al. 2019] is the same as
  `A₄ ≥ 18`. Theorem A needs this only for two-uniform states; in the summed shadow inequality
  the terms of the three-qubit reductions cancel. The graph state used for the lower bound has
  average four-qubit purity exactly `1/14` (112, 12 and 2 reductions of purity `1/16`, `1/8`,
  `1/4`).
- **Covering arguments.** The bound 120 of [ZNSZ 2025] comes from a Turán-type covering
  condition [ZNSZ 2025, Lemma 3]: for every six-set `T` some bad four-set `A` has
  `|A ∩ T| ∈ {1, 4}`. We checked that the minimum number of bad four-sets in this covering
  problem is 7 (six are impossible by a divisibility count; seven are attained by the complements
  of the lines of a Fano plane inside a seven-point set), so the covering condition alone cannot
  give an upper bound below 119. The proof here does not use it.
- **Graph states.** For a graph state, the reduction to `A` is maximally mixed exactly when the
  cut matrix `Γ[A, Aᶜ]` has full rank over GF(2); [ZNSZ 2025] uses this criterion for its lower
  bounds, and representatives of all connected nine-vertex graph states up to local Clifford
  equivalence are in the database of [Danielsen–Parker 2006].
- **Extremal set theory.** Theorem A uses the Kneser graph `KG(9,4)`, and Theorem C the
  Kruskal–Katona theorem [Kruskal 1963; Katona 1968], which is available in Mathlib.
- **Formalizations.** Formal Conjectures states the existence problem of AME states as
  `OpenQuantumProblems/35.lean`; several of its cases, such as AME(4,3), AME(9,6) and AME(11,10),
  are linked to Lean proofs.

In short:

- ✅ **Known before this repository:** `Qex(n)` for every `n ≤ 8`.
- 🆕 **This repository:** `Qex(9) = 112`, whose upper bound to our knowledge was not proved before,
  and the upper bounds `Qex(10) ≤ 208` and `Qex(11) ≤ 422`, all with kernel-checked Lean proofs.
- ❓ **Still open:** `Qex(10)`, `Qex(11)`, `Qex(12)` and every `n ≥ 13`.
