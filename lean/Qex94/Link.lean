import Qex94.Basic

/-!
# The purity of the reduced density matrix

`purC ψ A` is the purity `Tr ρ_A²` of the reduced density matrix `ρ_A = reducedDensity A ψ`.
Consequently a normalized state has `purC ψ ∅ = 1`, and a maximally mixed reduction on `A`
has the minimal purity `2^{-|A|}`.
-/

open scoped BigOperators

namespace QuantumExtremalNumber

variable {n : ℕ}

/-- Gluing a configuration on `A` and a configuration on the complement of `A`. -/
abbrev glue (A : Finset (Fin n)) :
    (({i // i ∈ A} → Fin 2) × ({i // i ∉ A} → Fin 2)) ≃ Config n :=
  (Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Fin 2).symm

lemma mix_glue (A : Finset (Fin n)) (a a' : {i // i ∈ A} → Fin 2)
    (b b' : {i // i ∉ A} → Fin 2) :
    mix A (glue A (a, b)) (glue A (a', b')) = glue A (a', b) := by
  funext i
  by_cases h : i ∈ A <;> simp [mix, Equiv.piEquivPiSubtypeProd_symm_apply, h]

lemma sum_config_eq_sum_glue {M : Type*} [AddCommMonoid M] (A : Finset (Fin n))
    (f : Config n → M) :
    ∑ x, f x = ∑ a : {i // i ∈ A} → Fin 2, ∑ b : {i // i ∉ A} → Fin 2, f (glue A (a, b)) := by
  rw [← (glue A).sum_comp f, Fintype.sum_prod_type]

/-- `purC ψ A = Tr (ρ_A ρ_A)`. -/
lemma purC_eq_sum_reducedDensity (ψ : StateVector n) (A : Finset (Fin n)) :
    purC ψ A = ∑ a, ∑ a', reducedDensity A ψ a a' * reducedDensity A ψ a' a := by
  have h1 : purC ψ A = ∑ a, ∑ b, ∑ a', ∑ b', (ψ (glue A (a, b)) * ψ (glue A (a', b')) *
      star (ψ (glue A (a', b))) * star (ψ (glue A (a, b')))) := by
    unfold purC
    rw [sum_config_eq_sum_glue A]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [sum_config_eq_sum_glue A]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [mix_glue, mix_glue]
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [reducedDensity_apply, reducedDensity_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

lemma card_subconfig (A : Finset (Fin n)) :
    Fintype.card ({i // i ∈ A} → Fin 2) = 2 ^ A.card := by
  simp

/-- A maximally mixed reduction on `A` has the minimal purity `2^{-|A|}`. -/
lemma purC_of_isMaximallyMixedOn (ψ : StateVector n) (A : Finset (Fin n))
    (h : IsMaximallyMixedOn A ψ) : purC ψ A = ((2 : ℂ) ^ A.card)⁻¹ := by
  rw [purC_eq_sum_reducedDensity, h]
  have hentry : ∀ a a' : {i // i ∈ A} → Fin 2,
      (((2 : ℂ) ^ A.card)⁻¹ • (1 : Matrix ({i // i ∈ A} → Fin 2) ({i // i ∈ A} → Fin 2) ℂ))
          a a' *
        (((2 : ℂ) ^ A.card)⁻¹ • (1 : Matrix ({i // i ∈ A} → Fin 2) ({i // i ∈ A} → Fin 2) ℂ))
          a' a =
      if a = a' then ((2 : ℂ) ^ A.card)⁻¹ * ((2 : ℂ) ^ A.card)⁻¹ else 0 := by
    intro a a'
    by_cases haa : a = a'
    · subst haa
      simp
    · simp [haa, Ne.symm haa]
  simp_rw [hentry, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, card_subconfig, nsmul_eq_mul]
  push_cast
  field_simp

lemma pur_of_isMaximallyMixedOn (ψ : StateVector n) (A : Finset (Fin n))
    (h : IsMaximallyMixedOn A ψ) : pur ψ A = (1 / 2) ^ A.card := by
  rw [pur, purC_of_isMaximallyMixedOn ψ A h]
  rw [show ((2 : ℂ) ^ A.card)⁻¹ = (((1 / 2 : ℝ) ^ A.card : ℝ) : ℂ) by
    push_cast
    simp [one_div, inv_pow]]
  exact Complex.ofReal_re _

lemma sum_norm_sq_of_norm_eq_one (ψ : StateVector n) (h : ‖ψ‖ = 1) :
    ∑ x, ‖ψ x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- A normalized state has purity `1` on the empty set. -/
lemma purC_empty_of_norm_eq_one (ψ : StateVector n) (h : ‖ψ‖ = 1) :
    purC ψ ∅ = 1 := by
  unfold purC
  simp only [mix_empty]
  have hxy : ∀ x y : Config n, ψ x * ψ y * star (ψ x) * star (ψ y) =
      (ψ x * star (ψ x)) * (ψ y * star (ψ y)) := fun _ _ => by ring
  simp_rw [hxy, ← Finset.sum_mul_sum]
  have hx : ∑ x, ψ x * star (ψ x) = ((∑ x, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    exact RCLike.mul_conj (ψ x)
  rw [hx, sum_norm_sq_of_norm_eq_one ψ h]
  simp

lemma pur_empty_of_norm_eq_one (ψ : StateVector n) (h : ‖ψ‖ = 1) :
    pur ψ ∅ = 1 := by
  simp [pur, purC_empty_of_norm_eq_one ψ h]

end QuantumExtremalNumber
