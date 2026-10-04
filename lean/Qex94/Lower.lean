import Qex94.Basic

/-!
# The lower bound: a nine-qubit graph state with 112 maximally mixed four-qubit reductions

The witness is the graph state of Danielsen's nine-vertex graph `H?SvCz}` with adjacency
matrix `Γ`: its amplitudes are `ψ x = c · (-1) ^ q(x)`, where `q(x) = ∑_{ij ∈ E} x_i x_j`
over `𝔽₂` and `c = (1 + i) / 32` (so `|c|² = 2⁻⁹` without square roots).

For a set `A` of qubits and configurations `a, a'` on `A`, flipping an outside qubit `k`
multiplies the summand `ψ(a, b) · conj ψ(a', b)` of `ρ_A(a, a')` by
`(-1) ^ ∑_{j ∈ A} Γ k j (a_j + a'_j)`, which does not depend on the environment `b`.
If this sign is `-1` for some `k ∉ A`, the entry `ρ_A(a, a')` vanishes. The finite cut
criterion `CutOK A` guarantees such a `k` for all `a ≠ a'`; the diagonal entries are
`2⁵ · 2⁻⁹ = 1/16`. A kernel computation shows that `112` of the `126` four-sets of qubits
pass the criterion.
-/

open scoped BigOperators

namespace QuantumExtremalNumber

namespace LowerBound

/-- Adjacency matrix of Danielsen's graph `H?SvCz}` (vertices `0, …, 8`). -/
def adj : Fin 9 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 0, 0]]

/-- The cut criterion for a set `A` of qubits: there is no nonempty `D ⊆ A` such that every
qubit outside `A` has an even number of neighbours in `D`. Equivalently, the cut matrix
`Γ[Aᶜ, A]` has full column rank over `𝔽₂`. It is phrased with `filter` and `card` so that
the kernel evaluates it quickly. -/
def CutOK (A : Finset (Fin 9)) : Prop :=
  (A.powerset.filter (fun D => D.Nonempty ∧ ∀ k ∈ Aᶜ, (∑ j ∈ D, adj k j) = 0)).card = 0

instance : DecidablePred CutOK := fun _ => Nat.decEq _ _

/-- Exactly `112` of the `126` four-sets of qubits pass the cut criterion. -/
theorem card_filter_cutOK :
    ((Finset.powersetCard 4 (Finset.univ : Finset (Fin 9))).filter CutOK).card = 112 := by
  decide +kernel

/-- The cut criterion provides, for every nonempty `D ⊆ A`, a qubit outside `A` with an odd
number of neighbours in `D`. -/
theorem CutOK.exists_ne_zero {A D : Finset (Fin 9)} (hA : CutOK A) (hDA : D ⊆ A)
    (hD : D.Nonempty) : ∃ k ∉ A, (∑ j ∈ D, adj k j) ≠ 0 := by
  have h := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hA)
    (Finset.mem_powerset.mpr hDA)
  push Not at h
  obtain ⟨k, hk, hsum⟩ := h hD
  exact ⟨k, Finset.mem_compl.mp hk, hsum⟩

section Algebra

open Fin.CommRing

/-- The quadratic form of the graph: the sum of `x i * x j` over its eighteen edges. -/
def phase (x : Config 9) : Fin 2 :=
  x 0 * x 6 + x 0 * x 7 + x 0 * x 8 + x 1 * x 4 + x 1 * x 6 + x 1 * x 8 +
  x 2 * x 5 + x 2 * x 6 + x 2 * x 8 + x 3 * x 4 + x 3 * x 5 + x 3 * x 7 + x 3 * x 8 +
  x 4 * x 7 + x 4 * x 8 + x 5 * x 7 + x 5 * x 8 + x 6 * x 8

/-- Flipping qubit `k` changes the phase by the parity of `x` on the neighbourhood of `k`. -/
theorem phase_add_single (x : Config 9) (k : Fin 9) :
    phase (x + Pi.single k 1) = phase x + ∑ j, adj k j * x j := by
  fin_cases k <;> simp [phase, Fin.sum_univ_succ, adj] <;> ring

theorem fin2_add_self : ∀ u : Fin 2, u + u = 0 := by decide

theorem fin2_add_eq_ite : ∀ u v : Fin 2, u + v = if u ≠ v then 1 else 0 := by decide

theorem fin2_eq_one_of_ne_zero : ∀ u : Fin 2, u ≠ 0 → u = 1 := by decide

/-- The sign `(-1) ^ u` of a bit `u`. -/
def sgn (u : Fin 2) : ℂ := if u = 0 then 1 else -1

theorem sgn_add (u v : Fin 2) : sgn (u + v) = sgn u * sgn v := by
  fin_cases u <;> fin_cases v <;> simp [sgn]

theorem sgn_one : sgn 1 = -1 := by
  simp [sgn]

theorem star_sgn (u : Fin 2) : star (sgn u) = sgn u := by
  unfold sgn
  split_ifs <;> simp

theorem norm_sgn (u : Fin 2) : ‖sgn u‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

/-- The common amplitude `(1 + i) / 32`; its squared modulus is `1 / 512 = 2⁻⁹`. -/
noncomputable def amp : ℂ := ⟨1 / 32, 1 / 32⟩

theorem amp_mul_star : amp * star amp = 1 / 512 := by
  rw [Complex.star_def, Complex.mul_conj, amp, Complex.normSq_mk]
  norm_num

theorem norm_amp_sq : ‖amp‖ ^ 2 = 1 / 512 := by
  rw [Complex.sq_norm, amp, Complex.normSq_mk]
  norm_num

/-- The graph state: every amplitude is `amp` times the sign of the graph's quadratic form. -/
noncomputable def gstate : StateVector 9 :=
  WithLp.toLp 2 (fun x => amp * sgn (phase x))

theorem gstate_apply (x : Config 9) : gstate x = amp * sgn (phase x) := rfl

theorem gstate_normalized : ‖gstate‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h (x : Config 9) : ‖gstate.ofLp x‖ ^ 2 = 1 / 512 := by
    change ‖amp * sgn (phase x)‖ ^ 2 = 1 / 512
    rw [norm_mul, norm_sgn, mul_one, norm_amp_sq]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- Gluing a configuration on `A` with one on the complement of `A`, as in `reducedDensity`. -/
abbrev glue (A : Finset (Fin 9)) (a : {i // i ∈ A} → Fin 2) (b : {i // i ∉ A} → Fin 2) :
    Config 9 :=
  (Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Fin 2).symm (a, b)

theorem glue_of_mem (A : Finset (Fin 9)) (a : {i // i ∈ A} → Fin 2) (b : {i // i ∉ A} → Fin 2)
    (i : Fin 9) (h : i ∈ A) : glue A a b i = a ⟨i, h⟩ := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, h]

theorem glue_of_not_mem (A : Finset (Fin 9)) (a : {i // i ∈ A} → Fin 2)
    (b : {i // i ∉ A} → Fin 2) (i : Fin 9) (h : i ∉ A) : glue A a b i = b ⟨i, h⟩ := by
  simp [glue, Equiv.piEquivPiSubtypeProd_symm_apply, h]

/-- Flipping the outside qubit `k` of the environment flips qubit `k` of the glued
configuration. -/
theorem glue_add_single (A : Finset (Fin 9)) (a : {i // i ∈ A} → Fin 2)
    (b : {i // i ∉ A} → Fin 2) (k : {i // i ∉ A}) :
    glue A a (b + Pi.single k 1) = glue A a b + Pi.single k.1 1 := by
  funext i
  by_cases h : i ∈ A
  · have hik : i ≠ k.1 := fun e => k.2 (e ▸ h)
    rw [Pi.add_apply, glue_of_mem A a _ i h, glue_of_mem A a _ i h,
      Pi.single_eq_of_ne hik, add_zero]
  · rw [Pi.add_apply, glue_of_not_mem A a _ i h, glue_of_not_mem A a _ i h, Pi.add_apply]
    simp [Pi.single_apply, Subtype.ext_iff]

/-- Outside `A` the two glued configurations agree, so their sum only sees `a` and `a'`. -/
theorem glue_add_glue (A : Finset (Fin 9)) (a a' : {i // i ∈ A} → Fin 2)
    (b : {i // i ∉ A} → Fin 2) (j : Fin 9) :
    glue A a b j + glue A a' b j = glue A a 0 j + glue A a' 0 j := by
  by_cases h : j ∈ A
  · simp only [glue_of_mem A _ _ j h]
  · simp only [glue_of_not_mem A _ _ j h, Pi.zero_apply, fin2_add_self]

/-- A reduced matrix entry of the graph state, as a sign sum over the environment. -/
theorem reducedDensity_gstate (A : Finset (Fin 9)) (a a' : {i // i ∈ A} → Fin 2) :
    reducedDensity A gstate a a' =
      amp * star amp * ∑ b : {i // i ∉ A} → Fin 2,
        sgn (phase (glue A a b) + phase (glue A a' b)) := by
  simp only [reducedDensity_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [gstate_apply, gstate_apply, star_mul', star_sgn, sgn_add]
  ring

/-- On the diagonal every environment contributes `+1`. -/
theorem sum_sgn_diag (A : Finset (Fin 9)) (a : {i // i ∈ A} → Fin 2) :
    ∑ b : {i // i ∉ A} → Fin 2, sgn (phase (glue A a b) + phase (glue A a b)) =
      Fintype.card ({i // i ∉ A} → Fin 2) := by
  simp [fin2_add_self, sgn]

/-- If flipping the outside qubit `k` flips the sign of every summand, the environment sum
vanishes. -/
theorem sum_sgn_offdiag (A : Finset (Fin 9)) (a a' : {i // i ∈ A} → Fin 2)
    (k : {i // i ∉ A}) (hk : ∑ j, adj k.1 j * (glue A a 0 j + glue A a' 0 j) ≠ 0) :
    ∑ b : {i // i ∉ A} → Fin 2, sgn (phase (glue A a b) + phase (glue A a' b)) = 0 := by
  set F : ({i // i ∉ A} → Fin 2) → ℂ := fun b => sgn (phase (glue A a b) + phase (glue A a' b))
    with hF
  have key (b : {i // i ∉ A} → Fin 2) : F (b + Pi.single k 1) = - F b := by
    simp only [hF, glue_add_single, phase_add_single]
    have hsum : ∑ j, adj k.1 j * glue A a b j + ∑ j, adj k.1 j * glue A a' b j =
        ∑ j, adj k.1 j * (glue A a 0 j + glue A a' 0 j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_add, glue_add_glue]
    have hrw : phase (glue A a b) + ∑ j, adj k.1 j * glue A a b j +
        (phase (glue A a' b) + ∑ j, adj k.1 j * glue A a' b j) =
        (phase (glue A a b) + phase (glue A a' b)) +
          ∑ j, adj k.1 j * (glue A a 0 j + glue A a' 0 j) := by
      rw [← hsum]
      ring
    rw [hrw, sgn_add, fin2_eq_one_of_ne_zero _ hk, sgn_one]
    ring
  have hS : ∑ b, F b = -∑ b, F b := by
    calc ∑ b, F b = ∑ b, F (Equiv.addRight (Pi.single k 1) b) :=
          (Equiv.sum_comp (Equiv.addRight (Pi.single k 1)) F).symm
      _ = ∑ b, -F b := by
          apply Finset.sum_congr rfl
          intro b _
          exact key b
      _ = -∑ b, F b := Finset.sum_neg_distrib ..
  change ∑ b, F b = 0
  linear_combination hS / 2

/-- For two different configurations on a set passing the cut criterion, some outside qubit
sees an odd number of differences among its neighbours. -/
theorem exists_flip (A : Finset (Fin 9)) (hA : CutOK A) (a a' : {i // i ∈ A} → Fin 2)
    (hne : a ≠ a') :
    ∃ k : {i // i ∉ A}, ∑ j, adj k.1 j * (glue A a 0 j + glue A a' 0 j) ≠ 0 := by
  set D : Finset (Fin 9) := Finset.univ.filter (fun j => glue A a 0 j ≠ glue A a' 0 j) with hD
  have hDA : D ⊆ A := by
    intro j hj
    rw [hD, Finset.mem_filter] at hj
    by_contra h
    apply hj.2
    rw [glue_of_not_mem A _ _ j h, glue_of_not_mem A _ _ j h]
  have hDne : D.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨i.1, ?_⟩
    rw [hD, Finset.mem_filter, glue_of_mem A _ _ i.1 i.2, glue_of_mem A _ _ i.1 i.2]
    exact ⟨Finset.mem_univ _, hi⟩
  obtain ⟨k, hkA, hk⟩ := hA.exists_ne_zero hDA hDne
  refine ⟨⟨k, hkA⟩, ?_⟩
  convert hk using 1
  rw [hD, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [fin2_add_eq_ite]
  split_ifs <;> simp

/-- The environment of a four-set consists of five qubits. -/
theorem card_env (A : Finset (Fin 9)) (hcard : A.card = 4) :
    Fintype.card ({i // i ∉ A} → Fin 2) = 32 := by
  rw [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_coe, hcard]
  simp

/-- The graph state is maximally mixed on every four-set passing the cut criterion. -/
theorem maximallyMixed_of_cutOK (A : Finset (Fin 9)) (hcard : A.card = 4) (hA : CutOK A) :
    IsMaximallyMixedOn A gstate := by
  unfold IsMaximallyMixedOn
  ext a a'
  rw [reducedDensity_gstate, Matrix.smul_apply, hcard]
  by_cases h : a = a'
  · subst h
    rw [Matrix.one_apply_eq, sum_sgn_diag, card_env A hcard, amp_mul_star]
    norm_num
  · obtain ⟨k, hk⟩ := exists_flip A hA a a' h
    rw [Matrix.one_apply_ne h, sum_sgn_offdiag A a a' k hk]
    simp

end Algebra

end LowerBound

theorem exists_state_112 :
    ∃ ψ : StateVector 9, ‖ψ‖ = 1 ∧ 112 ≤ numMaximallyMixed 4 ψ := by
  refine ⟨LowerBound.gstate, LowerBound.gstate_normalized, ?_⟩
  rw [← LowerBound.card_filter_cutOK]
  unfold numMaximallyMixed
  apply Finset.card_le_card
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := LowerBound.maximallyMixed_of_cutOK A hA.1.2 hA.2
  rw [IsMaximallyMixedOn, hA.1.2] at h
  exact ⟨hA.1.2, h⟩

end QuantumExtremalNumber
