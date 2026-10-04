import Mathlib

/-!
# The combinatorial core

Everything quantum enters only through a real function `p` on subsets of nine qubits, the
purities of the reduced states. This file proves that four elementary properties of `p` allow
at most `112` four-sets with minimal purity `1/16`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.Abstract

/-! ### Elementary consequences of the hypotheses on `p` -/

/-- (D1) Adding one element at most doubles `p`. -/
lemma up_le (p : Finset (Fin 9) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (i : Fin 9) (T : Finset (Fin 9)) (hi : i ∉ T) : p (insert i T) ≤ 2 * p T := by
  have h1 : i ∉ (insert i T)ᶜ := by simp
  have h2 : insert i (insert i T)ᶜ = Tᶜ := by
    ext x
    by_cases hx : x = i
    · subst hx; simp [hi]
    · simp [hx]
  have := hloc i (insert i T)ᶜ h1
  rwa [h2, hcompl, hcompl] at this

/-- (D2) The lower bound `(1/2)^|T| ≤ p T`. -/
lemma half_pow_le (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (T : Finset (Fin 9)) : (1 / 2 : ℝ) ^ T.card ≤ p T := by
  induction T using Finset.induction_on with
  | empty => simp [h0]
  | insert i T hi ih =>
    rw [card_insert_of_notMem hi, pow_succ]
    have := hloc i T hi
    linarith

/-- (D3) Removing a set `D` multiplies `p` by at most `2^|D|`. -/
lemma le_two_pow_mul (p : Finset (Fin 9) → ℝ)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (D U : Finset (Fin 9)) (hDU : Disjoint D U) : p U ≤ 2 ^ D.card * p (D ∪ U) := by
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
lemma union_le_two_pow_mul (p : Finset (Fin 9) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (D U : Finset (Fin 9)) (hDU : Disjoint D U) : p (D ∪ U) ≤ 2 ^ D.card * p U := by
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
lemma eq_half_pow_of_subset (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (U S : Finset (Fin 9)) (hUS : U ⊆ S) (hS : p S = (1 / 2 : ℝ) ^ S.card) :
    p U = (1 / 2 : ℝ) ^ U.card := by
  apply le_antisymm _ (half_pow_le p h0 hloc U)
  have h1 := le_two_pow_mul p hloc (S \ U) U sdiff_disjoint
  rw [sdiff_union_of_subset hUS, hS] at h1
  have h2 : S.card = (S \ U).card + U.card := (card_sdiff_add_card_eq_card hUS).symm
  rw [h2, pow_add, ← mul_assoc, ← mul_pow] at h1
  norm_num at h1
  exact h1

/-! ### Counting four-sets -/

/-- A set `U` with `|U| ≤ 4` lies in at least `choose (9 - |U|) (4 - |U|)` four-sets. -/
lemma choose_le_card_supersets (U : Finset (Fin 9)) (hU : U.card ≤ 4) :
    Nat.choose (9 - U.card) (4 - U.card) ≤
      ((powersetCard 4 (univ : Finset (Fin 9))).filter (fun S => U ⊆ S)).card := by
  have h1 : (powersetCard (4 - U.card) Uᶜ).card = Nat.choose (9 - U.card) (4 - U.card) := by
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

/-! ### Level sums and the shadow inequality -/

/-- Sum of `p` over the `k`-subsets. -/
noncomputable def P (p : Finset (Fin 9) → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ powersetCard k (univ : Finset (Fin 9)), p T

/-- Complementation identifies the level sums `P p k` and `P p (9 - k)`. -/
lemma P_compl (p : Finset (Fin 9) → ℝ) (hcompl : ∀ T, p Tᶜ = p T) (k j : ℕ)
    (hkj : k + j = 9) : P p j = P p k := by
  unfold P
  apply Finset.sum_nbij' (fun T => Tᶜ) (fun T => Tᶜ)
  · intro T hT
    simp only [mem_powersetCard, subset_univ, true_and, card_compl, Fintype.card_fin] at hT ⊢
    omega
  · intro T hT
    simp only [mem_powersetCard, subset_univ, true_and, card_compl, Fintype.card_fin] at hT ⊢
    omega
  · intro T _; simp
  · intro T _; simp
  · intro T _; exact (hcompl T).symm

/-- Grouping the shadow sum by cardinality. -/
lemma sum_eq_sum_P (p : Finset (Fin 9) → ℝ) :
    ∑ T : Finset (Fin 9), (-1 : ℝ) ^ T.card * (9 - 2 * (T.card : ℝ)) * p T =
      ∑ k ∈ range 10, (-1 : ℝ) ^ k * (9 - 2 * (k : ℝ)) * P p k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 10) (g := Finset.card)
    (fun T _ => by
      rw [mem_range]; have := card_le_univ T; rw [Fintype.card_fin] at this; omega)]
  apply Finset.sum_congr rfl
  intro k _
  rw [univ_filter_card_eq, P, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [(mem_powersetCard.1 hT).2]

/-- The shadow inequality, once the first three level sums are known. -/
lemma shadow_ineq (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hshadow : 0 ≤ ∑ T : Finset (Fin 9), (-1 : ℝ) ^ T.card * (9 - 2 * (T.card : ℝ)) * p T)
    (h1 : P p 1 = 9 / 2) (h2 : P p 2 = 9) : 0 ≤ 45 - 6 * P p 3 + 2 * P p 4 := by
  rw [sum_eq_sum_P] at hshadow
  simp only [sum_range_succ, sum_range_zero] at hshadow
  norm_num at hshadow
  have e0 : P p 0 = 1 := by
    unfold P; rw [powersetCard_zero, sum_singleton, h0]
  have c9 := P_compl p hcompl 0 9 rfl
  have c8 := P_compl p hcompl 1 8 rfl
  have c7 := P_compl p hcompl 2 7 rfl
  have c6 := P_compl p hcompl 3 6 rfl
  have c5 := P_compl p hcompl 4 5 rfl
  linarith

lemma P_one (p : Finset (Fin 9) → ℝ) (h : ∀ U : Finset (Fin 9), U.card = 1 → p U = 1 / 2) :
    P p 1 = 9 / 2 := by
  unfold P
  rw [sum_congr rfl (fun U hU => h U (mem_powersetCard.1 hU).2), sum_const, card_powersetCard,
    card_univ, Fintype.card_fin]
  norm_num

lemma P_two (p : Finset (Fin 9) → ℝ) (h : ∀ U : Finset (Fin 9), U.card = 2 → p U = 1 / 4) :
    P p 2 = 9 := by
  unfold P
  rw [sum_congr rfl (fun U hU => h U (mem_powersetCard.1 hU).2), sum_const, card_powersetCard,
    card_univ, Fintype.card_fin]
  have : Nat.choose 9 2 = 36 := by decide
  rw [this]
  norm_num

/-- Double counting: every three-set is `S.erase i` for exactly six pairs `(S, i)`. -/
lemma sum_sum_erase (p : Finset (Fin 9) → ℝ) :
    ∑ S ∈ powersetCard 4 (univ : Finset (Fin 9)), ∑ i ∈ S, p (S.erase i) = 6 * P p 3 := by
  rw [Finset.sum_sigma']
  have : ∑ x ∈ (powersetCard 4 (univ : Finset (Fin 9))).sigma (fun S => S), p (x.1.erase x.2) =
      ∑ y ∈ (powersetCard 3 (univ : Finset (Fin 9))).sigma (fun T => Tᶜ), p y.1 := by
    apply Finset.sum_nbij' (fun x => ⟨x.1.erase x.2, x.2⟩) (fun y => ⟨insert y.2 y.1, y.2⟩)
    · simp only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_compl]
      rintro ⟨S, i⟩ ⟨h1, h2⟩
      exact ⟨by rw [card_erase_of_mem h2, h1], notMem_erase i S⟩
    · simp only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_compl]
      rintro ⟨T, j⟩ ⟨h1, h2⟩
      exact ⟨by rw [card_insert_of_notMem h2, h1], mem_insert_self _ _⟩
    · simp only [mem_sigma]
      rintro ⟨S, i⟩ ⟨_, h2⟩
      simp [insert_erase h2]
    · simp only [mem_sigma, mem_compl]
      rintro ⟨T, j⟩ ⟨_, h2⟩
      simp [erase_insert h2]
    · intro x _
      rfl
  rw [this, ← Finset.sum_sigma' (powersetCard 3 (univ : Finset (Fin 9))) (fun T => Tᶜ)
    (fun T _ => p T)]
  unfold P
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [sum_const, card_compl, Fintype.card_fin, (mem_powersetCard.1 hT).2]
  norm_num

/-! ### The Kneser-graph lemma -/

/-- The four-sets disjoint from `S` (the Kneser-graph neighbourhood of `S`). -/
def N (S : Finset (Fin 9)) : Finset (Finset (Fin 9)) :=
  (powersetCard 4 univ).filter (fun R => Disjoint R S)

lemma mem_N {R S : Finset (Fin 9)} : R ∈ N S ↔ R.card = 4 ∧ Disjoint R S := by
  simp [N, mem_powersetCard]

lemma card_N (S : Finset (Fin 9)) (hS : S.card = 4) : (N S).card = 5 := by
  have : N S = powersetCard 4 Sᶜ := by
    ext R
    rw [mem_N, mem_powersetCard, subset_compl_iff_disjoint_right, and_comm]
  rw [this, card_powersetCard, card_compl, Fintype.card_fin, hS]
  rfl

lemma notMem_N_self (S : Finset (Fin 9)) (hS : S.card = 4) : S ∉ N S := by
  rw [mem_N]
  rintro ⟨_, h⟩
  rw [disjoint_self_iff_empty] at h
  subst h
  simp at hS

lemma subset_compl_union {R S S' : Finset (Fin 9)} (h : Disjoint R S) (h' : Disjoint R S') :
    R ⊆ (S ∪ S')ᶜ := by
  rw [subset_compl_iff_disjoint_right, disjoint_union_right]
  exact ⟨h, h'⟩

lemma card_N_inter_le (S S' : Finset (Fin 9)) (hS : S.card = 4) (hS' : S'.card = 4)
    (hne : S ≠ S') : (N S ∩ N S').card ≤ 1 := by
  rw [card_le_one]
  intro R hR R' hR'
  rw [mem_inter, mem_N, mem_N] at hR hR'
  have hU : 5 ≤ (S ∪ S').card := by
    by_contra h
    rw [not_le] at h
    have h1 : S = S ∪ S' := eq_of_subset_of_card_le subset_union_left (by omega)
    have h2 : S' = S ∪ S' := eq_of_subset_of_card_le subset_union_right (by omega)
    exact hne (h1.trans h2.symm)
  have hc : (S ∪ S')ᶜ.card ≤ 4 := by
    rw [card_compl, Fintype.card_fin]; omega
  have e1 : R = (S ∪ S')ᶜ :=
    eq_of_subset_of_card_le (subset_compl_union hR.1.2 hR.2.2) (by omega)
  have e2 : R' = (S ∪ S')ᶜ :=
    eq_of_subset_of_card_le (subset_compl_union hR'.1.2 hR'.2.2) (by omega)
  rw [e1, e2]

lemma card_N_inter_eq_zero (S S' : Finset (Fin 9)) (hS : S.card = 4) (hS' : S'.card = 4)
    (hd : Disjoint S S') : (N S ∩ N S').card = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro R hR
  rw [mem_inter, mem_N, mem_N] at hR
  have hU : (S ∪ S').card = 8 := by rw [card_union_of_disjoint hd]; omega
  have := card_le_card (subset_compl_union hR.1.2 hR.2.2)
  rw [card_compl, Fintype.card_fin] at this
  omega

/-- Bonferroni's inequality for three sets. -/
lemma card_three_union {α : Type*} [DecidableEq α] (A B C : Finset α) :
    A.card + B.card + C.card ≤
      (A ∪ B ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  have h1 := card_union_add_card_inter A B
  have h2 := card_union_add_card_inter (A ∪ B) C
  have h3 : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [union_inter_distrib_right]; exact card_union_le _ _
  omega

lemma notMem_N_of_not_disjoint {S T : Finset (Fin 9)} (h : ¬ Disjoint S T) : S ∉ N T := by
  rw [mem_N]; exact fun h' => h h'.2

/-- Three distinct four-sets, together with their Kneser neighbourhoods, form at least 14
four-sets. -/
lemma kneser_three (S1 S2 S3 : Finset (Fin 9)) (h1 : S1.card = 4) (h2 : S2.card = 4)
    (h3 : S3.card = 4) (h12 : S1 ≠ S2) (h13 : S1 ≠ S3) (h23 : S2 ≠ S3) :
    14 ≤ (insert S1 (insert S2 (insert S3 (N S1 ∪ N S2 ∪ N S3)))).card := by
  set U := N S1 ∪ N S2 ∪ N S3 with hU
  set X := insert S1 (insert S2 (insert S3 U)) with hX
  have hUX : U ⊆ X := by
    intro x hx; rw [hX]; exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem hx))
  have hb := card_three_union (N S1) (N S2) (N S3)
  rw [card_N S1 h1, card_N S2 h2, card_N S3 h3, ← hU] at hb
  have i12 := card_N_inter_le S1 S2 h1 h2 h12
  have i13 := card_N_inter_le S1 S3 h1 h3 h13
  have i23 := card_N_inter_le S2 S3 h2 h3 h23
  have n1 := notMem_N_self S1 h1
  have n2 := notMem_N_self S2 h2
  have n3 := notMem_N_self S3 h3
  by_cases d12 : Disjoint S1 S2
  · have e12 := card_N_inter_eq_zero S1 S2 h1 h2 d12
    by_cases d13 : Disjoint S1 S3
    · have e13 := card_N_inter_eq_zero S1 S3 h1 h3 d13
      have := card_le_card hUX
      omega
    · by_cases d23 : Disjoint S2 S3
      · have e23 := card_N_inter_eq_zero S2 S3 h2 h3 d23
        have := card_le_card hUX
        omega
      · -- `S3` meets both `S1` and `S2`, so it is not in `U`
        have hS3 : S3 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          refine ⟨⟨notMem_N_of_not_disjoint ?_, notMem_N_of_not_disjoint ?_⟩, n3⟩
          · exact fun h => d13 h.symm
          · exact fun h => d23 h.symm
        have hsub : insert S3 U ⊆ X := by
          intro x hx
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hX]; exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
          · exact hUX hx
        have := card_le_card hsub
        rw [card_insert_of_notMem hS3] at this
        omega
  · by_cases d13 : Disjoint S1 S3
    · have e13 := card_N_inter_eq_zero S1 S3 h1 h3 d13
      by_cases d23 : Disjoint S2 S3
      · have e23 := card_N_inter_eq_zero S2 S3 h2 h3 d23
        have := card_le_card hUX
        omega
      · -- `S2` meets both `S1` and `S3`
        have hS2 : S2 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          refine ⟨⟨notMem_N_of_not_disjoint ?_, n2⟩, notMem_N_of_not_disjoint d23⟩
          exact fun h => d12 h.symm
        have hsub : insert S2 U ⊆ X := by
          intro x hx
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hX]; exact mem_insert_of_mem (mem_insert_self _ _)
          · exact hUX hx
        have := card_le_card hsub
        rw [card_insert_of_notMem hS2] at this
        omega
    · by_cases d23 : Disjoint S2 S3
      · have e23 := card_N_inter_eq_zero S2 S3 h2 h3 d23
        -- `S1` meets both `S2` and `S3`
        have hS1 : S1 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          exact ⟨⟨n1, notMem_N_of_not_disjoint d12⟩, notMem_N_of_not_disjoint d13⟩
        have hsub : insert S1 U ⊆ X := by
          intro x hx
          rw [mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hX]; exact mem_insert_self _ _
          · exact hUX hx
        have := card_le_card hsub
        rw [card_insert_of_notMem hS1] at this
        omega
      · -- no two of them are disjoint
        have hS1 : S1 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          exact ⟨⟨n1, notMem_N_of_not_disjoint d12⟩, notMem_N_of_not_disjoint d13⟩
        have hS2 : S2 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          refine ⟨⟨notMem_N_of_not_disjoint ?_, n2⟩, notMem_N_of_not_disjoint d23⟩
          exact fun h => d12 h.symm
        have hS3 : S3 ∉ U := by
          rw [hU]
          simp only [mem_union, not_or]
          refine ⟨⟨notMem_N_of_not_disjoint ?_, notMem_N_of_not_disjoint ?_⟩, n3⟩
          · exact fun h => d13 h.symm
          · exact fun h => d23 h.symm
        have c3 : (insert S3 U).card = U.card + 1 := card_insert_of_notMem hS3
        have c2 : (insert S2 (insert S3 U)).card = U.card + 2 := by
          rw [card_insert_of_notMem, c3]
          rw [mem_insert, not_or]; exact ⟨h23, hS2⟩
        have c1 : X.card = U.card + 3 := by
          rw [hX, card_insert_of_notMem, c2]
          rw [mem_insert, mem_insert, not_or, not_or]; exact ⟨h12, h13, hS1⟩
        omega

/-- If at most 13 four-sets are bad, then at most two bad four-sets have only bad
four-sets disjoint from them. -/
lemma card_H_le (B : Finset (Finset (Fin 9))) (hB : B ⊆ powersetCard 4 univ)
    (hBc : B.card ≤ 13) :
    (B.filter (fun S =>
      ∀ R ∈ powersetCard 4 (univ : Finset (Fin 9)), Disjoint R S → R ∈ B)).card ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨S1, hS1, S2, hS2, S3, hS3, h12, h13, h23⟩ := two_lt_card.1 h
  rw [mem_filter] at hS1 hS2 hS3
  have hc : ∀ S ∈ B, S.card = 4 := fun S hS => (mem_powersetCard.1 (hB hS)).2
  have hN : ∀ S, (S ∈ B ∧
      ∀ R ∈ powersetCard 4 (univ : Finset (Fin 9)), Disjoint R S → R ∈ B) →
      N S ⊆ B := by
    intro S hS R hR
    rw [N, mem_filter] at hR
    exact hS.2 R hR.1 hR.2
  have hsub : insert S1 (insert S2 (insert S3 (N S1 ∪ N S2 ∪ N S3))) ⊆ B := by
    intro x hx
    simp only [mem_insert, mem_union] at hx
    rcases hx with rfl | rfl | rfl | (hx | hx) | hx
    · exact hS1.1
    · exact hS2.1
    · exact hS3.1
    · exact hN S1 hS1 hx
    · exact hN S2 hS2 hx
    · exact hN S3 hS3 hx
  have := card_le_card hsub
  have := kneser_three S1 S2 S3 (hc _ hS1.1) (hc _ hS2.1) (hc _ hS3.1) h12 h13 h23
  omega

/-! ### The local quantity `a` -/

/-- The local quantity attached to a four-set `S`. -/
noncomputable def a (p : Finset (Fin 9) → ℝ) (S : Finset (Fin 9)) : ℝ :=
  16 * p S - 8 * ∑ i ∈ S, p (S.erase i) + 3

lemma a_le_three (p : Finset (Fin 9) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S : Finset (Fin 9)) (hS : S.card = 4) : a p S ≤ 3 := by
  unfold a
  have h : ∀ i ∈ S, p S ≤ 2 * p (S.erase i) := by
    intro i hi
    have := up_le p hcompl hloc i (S.erase i) (notMem_erase i S)
    rwa [insert_erase hi] at this
  have hsum := Finset.sum_le_sum h
  rw [sum_const, hS, ← Finset.mul_sum, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

lemma a_eq_zero (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S : Finset (Fin 9)) (hS : S.card = 4) (hp : p S = 1 / 16) : a p S = 0 := by
  unfold a
  have h : ∀ i ∈ S, p (S.erase i) = 1 / 8 := by
    intro i hi
    have := eq_half_pow_of_subset p h0 hloc (S.erase i) S (erase_subset i S)
      (by rw [hp, hS]; norm_num)
    rw [this, card_erase_of_mem hi, hS]
    norm_num
  rw [sum_congr rfl h, sum_const, hS, hp, nsmul_eq_mul]
  norm_num

lemma a_le_one (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S R : Finset (Fin 9)) (hS : S.card = 4) (hR : R.card = 4) (hRS : Disjoint R S)
    (hp : p R = 1 / 16) : a p S ≤ 1 := by
  unfold a
  have hpS : p S ≤ 1 / 8 := by
    rw [← hcompl S]
    have hsub : R ⊆ Sᶜ := subset_compl_iff_disjoint_right.2 hRS
    have h1 := union_le_two_pow_mul p hcompl hloc (Sᶜ \ R) R sdiff_disjoint
    rw [sdiff_union_of_subset hsub, hp] at h1
    have hc : (Sᶜ \ R).card = 1 := by
      have := card_sdiff_add_card_eq_card hsub
      rw [card_compl, Fintype.card_fin, hS, hR] at this
      omega
    rw [hc] at h1
    linarith
  have h : ∀ i ∈ S, 1 / 8 ≤ p (S.erase i) := by
    intro i hi
    have := half_pow_le p h0 hloc (S.erase i)
    rw [card_erase_of_mem hi, hS] at this
    norm_num at this
    linarith
  have hsum := Finset.sum_le_sum h
  rw [sum_const, hS, nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

/-- Upper bound for the sum of `a` when at most 13 four-sets are bad. -/
lemma sum_a_le (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : ((powersetCard 4 (univ : Finset (Fin 9))).filter (fun A => ¬ p A = 1 / 16)).card
      ≤ 13) :
    ∑ S ∈ powersetCard 4 (univ : Finset (Fin 9)), a p S ≤ 17 := by
  set 𝒮 := powersetCard 4 (univ : Finset (Fin 9)) with h𝒮
  set B := 𝒮.filter (fun A => ¬ p A = 1 / 16) with hBdef
  have hH := card_H_le B (filter_subset _ _) hB
  rw [← sum_filter_add_sum_filter_not 𝒮 (fun A => p A = 1 / 16)]
  have hG : ∑ S ∈ 𝒮.filter (fun A => p A = 1 / 16), a p S = 0 := by
    apply sum_eq_zero
    intro S hS
    rw [mem_filter, h𝒮, mem_powersetCard] at hS
    exact a_eq_zero p h0 hloc S hS.1.2 hS.2
  rw [hG, zero_add, ← hBdef]
  have hle : ∀ S ∈ B,
      a p S ≤ if (∀ R ∈ 𝒮, Disjoint R S → R ∈ B) then (3 : ℝ) else 1 := by
    intro S hS
    have hS4 : S.card = 4 := by
      rw [hBdef, mem_filter, h𝒮, mem_powersetCard] at hS
      exact hS.1.2
    split_ifs with hc
    · exact a_le_three p hcompl hloc S hS4
    · simp only [not_forall] at hc
      obtain ⟨R, hR, hRS, hRB⟩ := hc
      have hpR : p R = 1 / 16 := by
        rw [hBdef, mem_filter, not_and, not_not] at hRB
        exact hRB hR
      have hR4 : R.card = 4 := by
        rw [h𝒮, mem_powersetCard] at hR
        exact hR.2
      exact a_le_one p h0 hcompl hloc S R hS4 hR4 hRS hpR
  have hsplit := card_filter_add_card_filter_not (s := B)
    (fun S => ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)
  calc ∑ S ∈ B, a p S
      ≤ ∑ S ∈ B, (if (∀ R ∈ 𝒮, Disjoint R S → R ∈ B) then (3 : ℝ) else 1) :=
        sum_le_sum hle
    _ = 3 * ((B.filter (fun S => ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)).card : ℝ) +
          ((B.filter (fun S => ¬ ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)).card : ℝ) := by
        rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ 17 := by
        have e : ((B.filter (fun S => ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)).card : ℝ) +
            ((B.filter (fun S => ¬ ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)).card : ℝ) =
              B.card := by
          exact_mod_cast hsplit
        have hH' :
            ((B.filter (fun S => ∀ R ∈ 𝒮, Disjoint R S → R ∈ B)).card : ℝ) ≤ 2 := by
          exact_mod_cast hH
        have hB' : (B.card : ℝ) ≤ 13 := by exact_mod_cast hB
        linarith

/-! ### Assembling the argument -/

/-- At most 13 bad four-sets force `p U = (1/2)^|U|` for every `U` with `|U| ≤ 2`. -/
lemma uniform_of_few_bad (p : Finset (Fin 9) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : ((powersetCard 4 (univ : Finset (Fin 9))).filter (fun A => ¬ p A = 1 / 16)).card
      ≤ 13)
    (U : Finset (Fin 9)) (hU : U.card ≤ 2) : p U = (1 / 2 : ℝ) ^ U.card := by
  have hex : ∃ S ∈ powersetCard 4 (univ : Finset (Fin 9)), U ⊆ S ∧ p S = 1 / 16 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hsub : (powersetCard 4 (univ : Finset (Fin 9))).filter (fun S => U ⊆ S) ⊆
        (powersetCard 4 (univ : Finset (Fin 9))).filter (fun A => ¬ p A = 1 / 16) := by
      intro S hS
      rw [mem_filter] at hS ⊢
      exact ⟨hS.1, hne S hS.1 hS.2⟩
    have h1 := card_le_card hsub
    have h2 := choose_le_card_supersets U (by omega)
    have h3 : 21 ≤ Nat.choose (9 - U.card) (4 - U.card) := by
      obtain h | h | h : U.card = 0 ∨ U.card = 1 ∨ U.card = 2 := by omega
      all_goals rw [h]; decide
    omega
  obtain ⟨S, hS, hUS, hpS⟩ := hex
  apply eq_half_pow_of_subset p h0 hloc U S hUS
  rw [hpS, (mem_powersetCard.1 hS).2]
  norm_num

/-- The sum of `a` over all four-sets, in terms of level sums. -/
lemma sum_a_eq (p : Finset (Fin 9) → ℝ) :
    ∑ S ∈ powersetCard 4 (univ : Finset (Fin 9)), a p S = 16 * P p 4 - 48 * P p 3 + 378 := by
  unfold a
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sum_erase, sum_const,
    card_powersetCard, card_univ, Fintype.card_fin,
    show ∑ S ∈ powersetCard 4 (univ : Finset (Fin 9)), p S = P p 4 from rfl]
  have h : Nat.choose 9 4 = 126 := by decide
  rw [h, nsmul_eq_mul]
  push_cast
  ring

theorem abstract_bound (p : Finset (Fin 9) → ℝ)
    (h0 : p ∅ = 1)
    (hcompl : ∀ T, p Tᶜ = p T)
    (hshadow : 0 ≤ ∑ T : Finset (Fin 9), (-1 : ℝ) ^ T.card * (9 - 2 * (T.card : ℝ)) * p T)
    (hloc : ∀ (i : Fin 9) (W : Finset (Fin 9)), i ∉ W → p W ≤ 2 * p (insert i W)) :
    ((powersetCard 4 (univ : Finset (Fin 9))).filter (fun A => p A = 1 / 16)).card ≤ 112 := by
  by_contra hcon
  rw [not_le] at hcon
  -- at most `126 - 113 = 13` four-sets are bad
  have htot := card_filter_add_card_filter_not (s := powersetCard 4 (univ : Finset (Fin 9)))
    (fun A => p A = 1 / 16)
  rw [card_powersetCard, card_univ, Fintype.card_fin] at htot
  have h126 : Nat.choose 9 4 = 126 := by decide
  rw [h126] at htot
  have hB : ((powersetCard 4 (univ : Finset (Fin 9))).filter (fun A => ¬ p A = 1 / 16)).card
      ≤ 13 := by omega
  -- hence `p` is 2-uniform, which pins down `P p 1` and `P p 2`
  have huni := uniform_of_few_bad p h0 hloc hB
  have h1 : P p 1 = 9 / 2 := P_one p (fun U hU => by rw [huni U (by omega), hU]; norm_num)
  have h2 : P p 2 = 9 := P_two p (fun U hU => by rw [huni U (by omega), hU]; norm_num)
  -- the shadow inequality bounds `∑ a` from below, the local bounds from above
  have hsh := shadow_ineq p h0 hcompl hshadow h1 h2
  have hle := sum_a_le p h0 hcompl hloc hB
  rw [sum_a_eq] at hle
  linarith

end QuantumExtremalNumber.Abstract
