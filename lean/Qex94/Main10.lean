import Qex94.Abstract10
import Qex94.Shadow
import Qex94.Link
import Qex94.SignSums

/-!
# `Qex 10 5 ≤ 208`

Six copies of the shadow inequality with no `+` site, plus the shadow inequalities with `+`
sites `{i, j}` over all ordered pairs `i ≠ j`, give the single inequality
`∑ T, (-1)^|T| (|T| - 4) (|T| - 6) p T ≥ 0`. Its coefficients vanish at `|T| = 4, 6`.
The combinatorial core `Abstract10.abstract_bound_ten` then bounds the number of
five-sets with minimal purity.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber

variable {n : ℕ}

open SignSums

/-- The combined shadow inequality for ten qubits. -/
theorem shadow_ten (ψ : Config 10 → ℂ) :
    0 ≤ ∑ T : Finset (Fin 10),
      (-1 : ℝ) ^ T.card * (((T.card : ℝ) - 4) * ((T.card : ℝ) - 6)) * pur ψ T := by
  have h0 := shadow_nonneg_set ψ ∅
  simp only [prod_sign_empty] at h0
  have h2 : 0 ≤ ∑ i : Fin 10, ∑ j : Fin 10, (if i = j then 0 else
      ∑ T : Finset (Fin 10),
        (∏ l ∈ T, (if l ∈ ({i, j} : Finset (Fin 10)) then (1 : ℝ) else -1)) * pur ψ T) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact le_refl 0
    · exact shadow_nonneg_set ψ {i, j}
  have h2' : ∑ i : Fin 10, ∑ j : Fin 10, (if i = j then 0 else
      ∑ T : Finset (Fin 10),
        (∏ l ∈ T, (if l ∈ ({i, j} : Finset (Fin 10)) then (1 : ℝ) else -1)) * pur ψ T) =
      ∑ T : Finset (Fin 10),
        (-1 : ℝ) ^ T.card * (((10 : ℝ) - 2 * T.card) ^ 2 - 10) * pur ψ T := by
    have hij : ∀ i j : Fin 10, (if i = j then 0 else
        ∑ T : Finset (Fin 10),
          (∏ l ∈ T, (if l ∈ ({i, j} : Finset (Fin 10)) then (1 : ℝ) else -1)) * pur ψ T) =
        ∑ T : Finset (Fin 10),
          (-1 : ℝ) ^ T.card * (if i = j then 0 else sgnIn T i * sgnIn T j) * pur ψ T := by
      intro i j
      by_cases h : i = j
      · simp [h]
      · simp only [h, ite_false]
        exact Finset.sum_congr rfl fun T _ => by rw [prod_sign_pair T h]
    simp_rw [hij]
    rw [sum_three_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    have hT := sum_pair_sgnIn (n := 10) T
    push_cast at hT
    calc ∑ i : Fin 10, ∑ j : Fin 10,
          (-1 : ℝ) ^ T.card * (if i = j then 0 else sgnIn T i * sgnIn T j) * pur ψ T =
        (-1 : ℝ) ^ T.card *
          (∑ i : Fin 10, ∑ j : Fin 10, (if i = j then 0 else sgnIn T i * sgnIn T j)) *
            pur ψ T := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = (-1 : ℝ) ^ T.card * (((10 : ℝ) - 2 * T.card) ^ 2 - 10) * pur ψ T := by
          rw [hT]
  rw [h2'] at h2
  have hcomb : ∑ T : Finset (Fin 10),
      (-1 : ℝ) ^ T.card * (((T.card : ℝ) - 4) * ((T.card : ℝ) - 6)) * pur ψ T =
      (1 / 4) * ∑ T : Finset (Fin 10),
        (-1 : ℝ) ^ T.card * (((10 : ℝ) - 2 * T.card) ^ 2 - 10) * pur ψ T +
      (6 / 4) * ∑ T : Finset (Fin 10), (-1 : ℝ) ^ T.card * pur ψ T := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  rw [hcomb]
  linarith

/-- Every normalized ten-qubit state has at most `208` maximally mixed five-qubit
reductions. -/
theorem numMaximallyMixed_le_208 (ψ : StateVector 10) (hψ : ‖ψ‖ = 1) :
    numMaximallyMixed 5 ψ ≤ 208 := by
  have hb := Abstract10.abstract_bound_ten (pur ψ) (pur_empty_of_norm_eq_one ψ hψ)
    (pur_compl ψ) (shadow_ten ψ) (fun i W hi => pur_le_two_mul_pur_insert ψ W i hi)
  refine le_trans ?_ hb
  unfold numMaximallyMixed
  apply Finset.card_le_card
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨hA.1, ?_⟩
  rw [pur_of_isMaximallyMixedOn ψ A (by rw [IsMaximallyMixedOn, hA.1]; exact hA.2), hA.1]
  norm_num

/-- $\mathrm{Q}_{ex}(10) \le 208$. -/
theorem qex_ten.variants.upper : Qex 10 5 ≤ 208 := by
  refine csSup_le' ?_
  rintro m ⟨ψ, hψ, rfl⟩
  exact numMaximallyMixed_le_208 ψ hψ

end QuantumExtremalNumber
