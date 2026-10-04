import Mathlib

/-!
# Elementary consequences of the purity axioms, for any number of qubits

`p : Finset (Fin n) → ℝ` stands for the purities of the reduced states of a pure state.
The hypotheses used here are `p ∅ = 1`, complementarity `p Tᶜ = p T`, and the local bound
`p W ≤ 2 p (insert i W)`. These lemmas are the `n`-generic versions of the ones in
`Qex94/Abstract.lean`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.PurityFacts

variable {n : ℕ}

/-- (D1) Adding one element at most doubles `p`. -/
lemma up_le (p : Finset (Fin n) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin n) (W : Finset (Fin n)), i ∉ W → p W ≤ 2 * p (insert i W))
    (i : Fin n) (T : Finset (Fin n)) (hi : i ∉ T) : p (insert i T) ≤ 2 * p T := by
  have h1 : i ∉ (insert i T)ᶜ := by simp
  have h2 : insert i (insert i T)ᶜ = Tᶜ := by
    ext x
    by_cases hx : x = i
    · subst hx; simp [hi]
    · simp [hx]
  have := hloc i (insert i T)ᶜ h1
  rwa [h2, hcompl, hcompl] at this

/-- (D2) The lower bound `(1/2)^|T| ≤ p T`. -/
lemma half_pow_le (p : Finset (Fin n) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin n) (W : Finset (Fin n)), i ∉ W → p W ≤ 2 * p (insert i W))
    (T : Finset (Fin n)) : (1 / 2 : ℝ) ^ T.card ≤ p T := by
  induction T using Finset.induction_on with
  | empty => simp [h0]
  | insert i T hi ih =>
    rw [card_insert_of_notMem hi, pow_succ]
    have := hloc i T hi
    linarith

/-- (D3) Removing a set `D` multiplies `p` by at most `2^|D|`. -/
lemma le_two_pow_mul (p : Finset (Fin n) → ℝ)
    (hloc : ∀ (i : Fin n) (W : Finset (Fin n)), i ∉ W → p W ≤ 2 * p (insert i W))
    (D U : Finset (Fin n)) (hDU : Disjoint D U) : p U ≤ 2 ^ D.card * p (D ∪ U) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert i D hi ih =>
    rw [Finset.disjoint_insert_left] at hDU
    have hiU : i ∉ D ∪ U := by
      simp only [mem_union, not_or]; exact ⟨hi, hDU.1⟩
    have h1 := ih hDU.2
    have h2 := hloc i (D ∪ U) hiU
    rw [card_insert_of_notMem hi, insert_union, pow_succ]
    have h3 : (0 : ℝ) ≤ 2 ^ D.card := by positivity
    nlinarith

/-- (D3') Adding a set `D` multiplies `p` by at most `2^|D|`. -/
lemma union_le_two_pow_mul (p : Finset (Fin n) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin n) (W : Finset (Fin n)), i ∉ W → p W ≤ 2 * p (insert i W))
    (D U : Finset (Fin n)) (hDU : Disjoint D U) : p (D ∪ U) ≤ 2 ^ D.card * p U := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert i D hi ih =>
    rw [Finset.disjoint_insert_left] at hDU
    have hiU : i ∉ D ∪ U := by
      simp only [mem_union, not_or]; exact ⟨hi, hDU.1⟩
    have h1 := ih hDU.2
    have h2 := up_le p hcompl hloc i (D ∪ U) hiU
    rw [card_insert_of_notMem hi, insert_union, pow_succ]
    linarith

/-- (D4) Subsets of a set of minimal purity have minimal purity. -/
lemma eq_half_pow_of_subset (p : Finset (Fin n) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin n) (W : Finset (Fin n)), i ∉ W → p W ≤ 2 * p (insert i W))
    (U S : Finset (Fin n)) (hUS : U ⊆ S) (hS : p S = (1 / 2 : ℝ) ^ S.card) :
    p U = (1 / 2 : ℝ) ^ U.card := by
  apply le_antisymm _ (half_pow_le p h0 hloc U)
  have h1 := le_two_pow_mul p hloc (S \ U) U sdiff_disjoint
  rw [sdiff_union_of_subset hUS, hS] at h1
  have h2 : S.card = (S \ U).card + U.card := (card_sdiff_add_card_eq_card hUS).symm
  rw [h2, pow_add, ← mul_assoc, ← mul_pow] at h1
  norm_num at h1
  exact h1

/-- A set `U` with `|U| ≤ k` lies in at least `choose (n - |U|) (k - |U|)` sets of size `k`. -/
lemma choose_le_card_supersets (k : ℕ) (U : Finset (Fin n)) (hU : U.card ≤ k) :
    Nat.choose (n - U.card) (k - U.card) ≤
      ((powersetCard k (univ : Finset (Fin n))).filter (fun S => U ⊆ S)).card := by
  have h1 : (powersetCard (k - U.card) Uᶜ).card = Nat.choose (n - U.card) (k - U.card) := by
    rw [card_powersetCard, card_compl, Fintype.card_fin]
  rw [← h1]
  apply card_le_card_of_injOn (fun T => T ∪ U)
  · intro T hT
    simp only [mem_coe, mem_powersetCard, mem_filter, subset_univ, true_and] at hT ⊢
    have hd : Disjoint T U := subset_compl_iff_disjoint_right.1 hT.1
    refine ⟨?_, subset_union_right⟩
    rw [card_union_of_disjoint hd, hT.2]
    omega
  · intro T hT T' hT' h
    simp only [mem_coe, mem_powersetCard] at hT hT'
    have hd : Disjoint T U := subset_compl_iff_disjoint_right.1 hT.1
    have hd' : Disjoint T' U := subset_compl_iff_disjoint_right.1 hT'.1
    have e := congrArg (· \ U) h
    simp only at e
    rwa [union_sdiff_cancel_right hd, union_sdiff_cancel_right hd'] at e

/-- Sum of `p` over the `k`-subsets. -/
noncomputable def P (p : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ powersetCard k (univ : Finset (Fin n)), p T

/-- Complementation identifies the level sums `P p k` and `P p (n - k)`. -/
lemma P_compl (p : Finset (Fin n) → ℝ) (hcompl : ∀ T, p Tᶜ = p T) (k j : ℕ)
    (hkj : k + j = n) : P p j = P p k := by
  unfold P
  apply Finset.sum_nbij' (fun T => Tᶜ) (fun T => Tᶜ)
  · intro T hT
    simp only [mem_powersetCard, subset_univ, true_and] at hT ⊢
    rw [card_compl, Fintype.card_fin]
    omega
  · intro T hT
    simp only [mem_powersetCard, subset_univ, true_and] at hT ⊢
    rw [card_compl, Fintype.card_fin]
    omega
  · intro T _
    simp
  · intro T _
    simp
  · intro T _
    exact (hcompl T).symm

/-- Grouping a sum over all subsets by cardinality. -/
lemma sum_eq_sum_P (p : Finset (Fin n) → ℝ) (c : ℕ → ℝ) :
    ∑ T : Finset (Fin n), c T.card * p T = ∑ k ∈ range (n + 1), c k * P p k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1)) (g := Finset.card)
    (fun T _ => by
      rw [mem_range, Nat.lt_succ_iff]
      simpa using card_le_univ T)]
  refine sum_congr rfl fun k _ => ?_
  unfold P
  rw [mul_sum]
  refine sum_congr ?_ fun T hT => ?_
  · ext T
    simp [mem_powersetCard]
  · rw [(mem_powersetCard.1 hT).2]

/-- If every `k`-set has the value `v`, the level sum is `choose n k * v`. -/
lemma P_const (p : Finset (Fin n) → ℝ) (k : ℕ) (v : ℝ)
    (h : ∀ U : Finset (Fin n), U.card = k → p U = v) : P p k = n.choose k * v := by
  unfold P
  rw [sum_congr rfl (fun U hU => h U (mem_powersetCard.1 hU).2), sum_const, card_powersetCard,
    card_univ, Fintype.card_fin, nsmul_eq_mul]

end QuantumExtremalNumber.PurityFacts
