import Qex94.Statement

/-!
# Coordinate mixing and the purity of a reduced state

For a finite set `T` of qubits, `mix T x y` is the configuration that agrees with `y` on `T`
and with `x` off `T`. The purity `Tr ρ_T²` of the reduced state on `T` is the four-fold
amplitude sum `purC ψ T = ∑ x y, ψ x ψ y conj(ψ (mix T x y)) conj(ψ (mix T y x))`.
-/

open scoped BigOperators

namespace QuantumExtremalNumber

/-- A configuration of `n` qubits in the computational basis. -/
abbrev Config (n : ℕ) := Fin n → Fin 2

/-- A state of `n` qubits, given by its amplitudes in the computational basis. -/
abbrev StateVector (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

/-- The reduced state on `A` is maximally mixed: `ρ_A = I / 2^|A|`. -/
def IsMaximallyMixedOn {n : ℕ} (A : Finset (Fin n)) (ψ : StateVector n) : Prop :=
  reducedDensity A ψ = ((2 : ℂ) ^ A.card)⁻¹ • 1

/-- The entries of `reducedDensity A ψ = M Mᴴ` as a sum over the configurations outside `A`. -/
lemma reducedDensity_apply {n : ℕ} (A : Finset (Fin n)) (ψ : StateVector n)
    (a a' : {i // i ∈ A} → Fin 2) :
    reducedDensity A ψ a a' = ∑ b : {i // i ∉ A} → Fin 2,
      ψ ((Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Fin 2).symm (a, b)) *
        star (ψ ((Equiv.piEquivPiSubtypeProd (· ∈ A) fun _ => Fin 2).symm (a', b))) :=
  rfl

variable {n : ℕ}

/-- `mix T x y` agrees with `y` on `T` and with `x` off `T`. -/
def mix (T : Finset (Fin n)) (x y : Config n) : Config n :=
  fun i => if i ∈ T then y i else x i

@[simp] lemma mix_apply (T : Finset (Fin n)) (x y : Config n) (i : Fin n) :
    mix T x y i = if i ∈ T then y i else x i := rfl

lemma mix_compl (T : Finset (Fin n)) (x y : Config n) : mix Tᶜ x y = mix T y x := by
  funext i
  by_cases h : i ∈ T <;> simp [mix, h]

@[simp] lemma mix_empty (x y : Config n) : mix ∅ x y = x := by
  funext i
  simp [mix]

/-- The purity `Tr ρ_T²` of the reduced state on `T`, as a four-fold amplitude sum. -/
noncomputable def purC (ψ : Config n → ℂ) (T : Finset (Fin n)) : ℂ :=
  ∑ x, ∑ y, ψ x * ψ y * star (ψ (mix T x y)) * star (ψ (mix T y x))

/-- The real part of `purC`. -/
noncomputable def pur (ψ : Config n → ℂ) (T : Finset (Fin n)) : ℝ :=
  (purC ψ T).re

/-- Complementary purity: a global pure state has equal purities on `T` and on `Tᶜ`. -/
lemma purC_compl (ψ : Config n → ℂ) (T : Finset (Fin n)) : purC ψ Tᶜ = purC ψ T := by
  unfold purC
  simp only [mix_compl]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma pur_compl (ψ : Config n → ℂ) (T : Finset (Fin n)) : pur ψ Tᶜ = pur ψ T := by
  simp [pur, purC_compl]

end QuantumExtremalNumber
