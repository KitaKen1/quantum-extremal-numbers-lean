import FormalConjecturesUtil

/-!
# Quantum extremal numbers of qubit pure states (statement)

This module copies the definitions and the target statement of
`FormalConjectures/Arxiv/2411.12208/QuantumExtremalNumber.lean` verbatim (without the module
system header). The proof of the answer is in the other modules of this project.

For a pure state $\psi$ of $n$ qubits and $k \le n$, let $m_k(\psi)$ be the number of
$k$-element sets $A$ of qubits whose reduced density matrix $\rho_A$ is maximally mixed,
that is, $\rho_A = I / 2^k$. The quantum extremal number $\mathrm{Q}_{ex}(n, k)$ is the
maximum of $m_k(\psi)$ over all pure $n$-qubit states.

*Reference:* W. Zhang, Y. Ning, F. Shi, and X. Zhang, *Extremal Maximal Entanglement*,
Phys. Rev. A 111, 052410 (2025), [arXiv:2411.12208](https://arxiv.org/abs/2411.12208).
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

end QuantumExtremalNumber
