import Qex94.Abstract
import Qex94.Shadow
import Qex94.Link
import Qex94.Lower

/-!
# `Qex 9 4 = 112`

The upper bound combines the four purity facts (normalization, complementary purity, the
shadow inequality and the local bound) with the combinatorial core `Abstract.abstract_bound`.
The lower bound is the explicit graph state of `Lower.lean`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber

variable {n : ℕ}

lemma prod_sign (T : Finset (Fin n)) (i : Fin n) :
    ∏ l ∈ T, (if l = i then (1 : ℝ) else -1) = (-1) ^ (T.erase i).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne']

lemma sum_prod_sign (T : Finset (Fin n)) :
    ∑ i : Fin n, ∏ l ∈ T, (if l = i then (1 : ℝ) else -1) =
      (-1) ^ T.card * (n - 2 * (T.card : ℝ)) := by
  simp_rw [prod_sign]
  rw [← Finset.sum_add_sum_compl T]
  have h1 : ∀ i ∈ T, (-1 : ℝ) ^ (T.erase i).card = - (-1) ^ T.card := by
    intro i hi
    rw [Finset.card_erase_of_mem hi]
    obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by
      have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring
  have h2 : ∀ i ∈ Tᶜ, (-1 : ℝ) ^ (T.erase i).card = (-1) ^ T.card := by
    intro i hi
    rw [Finset.erase_eq_of_notMem (Finset.mem_compl.mp hi)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    Finset.card_compl, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hle : T.card ≤ n := by simpa using Finset.card_le_univ T
  rw [Nat.cast_sub hle]
  ring

/-- Summing the single-site shadow inequalities over all sites. -/
lemma shadow_sum (p : Finset (Fin n) → ℝ)
    (h : ∀ i, 0 ≤ ∑ T : Finset (Fin n), (∏ l ∈ T, (if l = i then (1 : ℝ) else -1)) * p T) :
    0 ≤ ∑ T : Finset (Fin n), (-1 : ℝ) ^ T.card * (n - 2 * (T.card : ℝ)) * p T := by
  have hsum : 0 ≤ ∑ i : Fin n, ∑ T : Finset (Fin n),
      (∏ l ∈ T, (if l = i then (1 : ℝ) else -1)) * p T :=
    Finset.sum_nonneg fun i _ => h i
  rw [Finset.sum_comm] at hsum
  simpa [← Finset.sum_mul, sum_prod_sign] using hsum

/-- Every normalized nine-qubit state has at most `112` maximally mixed four-qubit
reductions. -/
theorem numMaximallyMixed_le_112 (ψ : StateVector 9) (hψ : ‖ψ‖ = 1) :
    numMaximallyMixed 4 ψ ≤ 112 := by
  have hshadow := shadow_sum (pur ψ) (shadow_nonneg ψ)
  push_cast at hshadow
  have hb := Abstract.abstract_bound (pur ψ) (pur_empty_of_norm_eq_one ψ hψ) (pur_compl ψ)
    hshadow (fun i W hi => pur_le_two_mul_pur_insert ψ W i hi)
  refine le_trans ?_ hb
  unfold numMaximallyMixed
  apply Finset.card_le_card
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨hA.1, ?_⟩
  rw [pur_of_isMaximallyMixedOn ψ A (by rw [IsMaximallyMixedOn, hA.1]; exact hA.2), hA.1]
  norm_num

/-- The Formal Conjectures target: $\mathrm{Q}_{ex}(9) = 112$. -/
theorem qex_nine : Qex 9 4 = answer(112) := by
  obtain ⟨ψ, hψ, h112⟩ := exists_state_112
  apply IsGreatest.csSup_eq
  refine ⟨⟨ψ, hψ, le_antisymm (numMaximallyMixed_le_112 ψ hψ) h112⟩, ?_⟩
  rintro m ⟨φ, hφ, rfl⟩
  exact numMaximallyMixed_le_112 φ hφ

end QuantumExtremalNumber
