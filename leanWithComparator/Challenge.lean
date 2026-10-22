import FormalConjecturesUtil

/-!
Independent specification extracted from Formal Conjectures PR #6836 at
3ea4821704dfde365879d6a2d6f2f58e8f8d54e9. Only this file has challenge holes.
The solution lives in a separate import environment.
-/

open scoped BigOperators Matrix

namespace QuantumExtremalNumber

/-- The amplitudes of a state $\psi$ of `n` qubits, given in the computational basis
`Fin n → Fin 2`, as a matrix $M$: the rows are the configurations of the qubits in `A`, the
columns are the configurations of the other qubits. -/
noncomputable def amplitudeMatrix {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∉ A} → Fin 2) ℂ :=
  fun a b => ψ (fun i => if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, h⟩)

/-- The reduced density matrix $\rho_A = M M^*$ of $\psi$: the partial trace over the qubits
outside `A`. -/
noncomputable def reducedDensity {n : ℕ} (A : Finset (Fin n))
    (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) :
    Matrix ({i // i ∈ A} → Fin 2) ({i // i ∈ A} → Fin 2) ℂ :=
  amplitudeMatrix A ψ * (amplitudeMatrix A ψ)ᴴ

open scoped Classical in
/-- The number $m_k(\psi)$ of `k`-sets $A$ of qubits on which $\psi$ is maximally mixed,
$\rho_A = I / 2^k$. -/
noncomputable def numMaximallyMixed {n : ℕ} (k : ℕ) (ψ : EuclideanSpace ℂ (Fin n → Fin 2)) : ℕ :=
  (Finset.univ.filter fun A : Finset (Fin n) =>
    A.card = k ∧ reducedDensity A ψ = ((2 : ℂ) ^ k)⁻¹ • 1).card

/-- The quantum extremal number $\mathrm{Q}_{ex}(n, k)$: the largest $m_k(\psi)$ over the
normalized states $\psi$ of `n` qubits. -/
noncomputable def Qex (n k : ℕ) : ℕ :=
  sSup {m | ∃ ψ : EuclideanSpace ℂ (Fin n → Fin 2), ‖ψ‖ = 1 ∧ numMaximallyMixed k ψ = m}

/-- The exact nine-qubit target from the PR. -/
theorem qex_nine : Qex 9 4 = answer(112) := by
  sorry

/-- The ten-qubit upper bound cited by the PR. -/
theorem qex_ten.variants.upper : Qex 10 5 ≤ 208 := by
  sorry

/-- The eleven-qubit upper bound cited by the PR. -/
theorem qex_eleven.variants.upper : Qex 11 5 ≤ 422 := by
  sorry

end QuantumExtremalNumber
