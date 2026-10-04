import Qex94.Abstract11
import Qex94.KK11
import Qex94.Shadow
import Qex94.Link
import Qex94.SignSums

/-!
# `Qex 11 5 ≤ 422`

The inputs of the combinatorial core `Abstract11.abstract_bound_eleven` are the purity axioms,
the shadow inequality `6 S_3 ≥ 0` (a sum over ordered triples of distinct sites), the shadow
inequalities of all reduced states, the nonnegativity of the Möbius coefficients, and a
Kruskal–Katona bound for six-sets (`KK11.forty_le_card_shadow`).
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber

open SignSums

/-- The shadow inequality `6 S_3 ≥ 0` for eleven qubits, from the shadow inequalities with
`+` sites `{i, j, k}` over all ordered triples of distinct sites. -/
theorem shadow_eleven (ψ : Config 11 → ℂ) :
    0 ≤ ∑ T : Finset (Fin 11), (-1 : ℝ) ^ T.card *
      ((11 - 2 * (T.card : ℝ)) ^ 3 - 31 * (11 - 2 * (T.card : ℝ))) * pur ψ T := by
  have h3 : 0 ≤ ∑ i : Fin 11, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      ∑ T : Finset (Fin 11),
        (∏ l ∈ T, (if l ∈ ({i, j, k} : Finset (Fin 11)) then (1 : ℝ) else -1)) * pur ψ T :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      shadow_nonneg_set ψ {i, j, k}
  have hterm : ∀ i : Fin 11, ∀ j ∈ univ.erase i, ∀ k ∈ (univ.erase i).erase j,
      ∑ T : Finset (Fin 11),
        (∏ l ∈ T, (if l ∈ ({i, j, k} : Finset (Fin 11)) then (1 : ℝ) else -1)) * pur ψ T =
      ∑ T : Finset (Fin 11),
        (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T := by
    intro i j hj k hk
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [prod_sign_triple T hji.symm hkj.symm hki.symm]
  have hswap : ∑ i : Fin 11, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      ∑ T : Finset (Fin 11),
        (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T =
      ∑ T : Finset (Fin 11), (-1 : ℝ) ^ T.card *
        (∑ i : Fin 11, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
          sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T := by
    have h1 : ∀ i : Fin 11, ∀ j : Fin 11, ∑ k ∈ (univ.erase i).erase j,
        ∑ T : Finset (Fin 11),
          (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T =
        ∑ T : Finset (Fin 11), ∑ k ∈ (univ.erase i).erase j,
          (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T :=
      fun i j => Finset.sum_comm
    simp_rw [h1]
    have h2 : ∀ i : Fin 11, ∑ j ∈ univ.erase i, ∑ T : Finset (Fin 11),
        ∑ k ∈ (univ.erase i).erase j,
          (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T =
        ∑ T : Finset (Fin 11), ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
          (-1 : ℝ) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) * pur ψ T :=
      fun i => Finset.sum_comm
    simp_rw [h2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => hterm i j hj k hk, hswap] at h3
  refine h3.trans_eq (Finset.sum_congr rfl fun T _ => ?_)
  rw [sum_triple_sgnIn]
  push_cast
  ring

/-- Every normalized eleven-qubit state has at most `422` maximally mixed five-qubit
reductions. -/
theorem numMaximallyMixed_le_422 (ψ : StateVector 11) (hψ : ‖ψ‖ = 1) :
    numMaximallyMixed 5 ψ ≤ 422 := by
  have hb := Abstract11.abstract_bound_eleven (pur ψ) (pur_empty_of_norm_eq_one ψ hψ)
    (pur_compl ψ) (fun i W hi => pur_le_two_mul_pur_insert ψ W i hi) (shadow_eleven ψ)
    (subsystem_shadow_nonneg ψ) (moebius_nonneg ψ) KK11.forty_le_card_shadow
  refine le_trans ?_ hb
  unfold numMaximallyMixed
  apply Finset.card_le_card
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨hA.1, ?_⟩
  rw [pur_of_isMaximallyMixedOn ψ A (by rw [IsMaximallyMixedOn, hA.1]; exact hA.2), hA.1]
  norm_num

/-- $\mathrm{Q}_{ex}(11) \le 422$. -/
theorem qex_eleven.variants.upper : Qex 11 5 ≤ 422 := by
  refine csSup_le' ?_
  rintro m ⟨ψ, hψ, rfl⟩
  exact numMaximallyMixed_le_422 ψ hψ

end QuantumExtremalNumber
