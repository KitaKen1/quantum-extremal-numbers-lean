import Qex94.Basic

/-!
# Two-copy positivity: the shadow inequality and the local purity bound

Both inequalities come from one positivity principle. Write a pair of configurations `(x, y)`
sitewise as the pairs `(x l, y l) : Fin 2 × Fin 2`. For a two-copy vector
`Φ : Config n → Config n → ℂ` and a kernel `K`, consider the Hermitian form
`∑ x y x' y', conj (Φ x y) * K x y x' y' * Φ x' y'`. Suppose `K` is a product over the sites
of local kernels `k l`, and each `k l` is an integer Gram matrix,
`k l p p' = ∑ τ : Fin 5, v l τ p * v l τ p'`. Then `K` is a Gram matrix as well, so the form is
a sum of squared absolute values and is nonnegative (`twoCopyForm_gram_nonneg`).

* Shadow inequality: take `Φ = conj ψ ⊗ conj ψ` and `k l = I + η l • SWAP`, with `η i = 1` and
  `η l = -1` for `l ≠ i`. Expanding the product over the sites gives
  `∑ T, (∏ l ∈ T, η l) • [swap the two copies on T]`, so the form is
  `∑ T, (∏ l ∈ T, η l) * purC ψ T`. The Gram vectors of `I + SWAP` are `e₀₀, e₀₀, e₁₁, e₁₁`
  and `e₀₁ + e₁₀`; the one of `I - SWAP` is `e₀₁ - e₁₀`.
* Local purity bound: take `Φ = ψ ⊗ conj ψ`. The kernel with local factor `I` on `T` and
  `e eᵀ` off `T`, where `e (a, b) = [a = b]`, has the form `conj (purC ψ T)`. For `i ∉ W`, the
  kernel `2 K_{insert i W} - K_W` is again a product, with local factor `2 I - e eᵀ` at `i`.
  The Gram vectors of `2 I - e eᵀ` are `e₀₀ - e₁₁, e₀₁, e₀₁, e₁₀, e₁₀`.
-/

open scoped BigOperators

namespace QuantumExtremalNumber

variable {n : ℕ}

/- The Hermitian form of a kernel on two copies -/

/-- The Hermitian form `∑ x y x' y', conj (Φ x y) * K x y x' y' * Φ x' y'`. -/
private noncomputable def twoCopyForm (Φ : Config n → Config n → ℂ)
    (K : Config n → Config n → Config n → Config n → ℂ) : ℂ :=
  ∑ x, ∑ y, ∑ x', ∑ y', star (Φ x y) * K x y x' y' * Φ x' y'

private lemma twoCopyForm_sum {ι : Type*} (s : Finset ι) (Φ : Config n → Config n → ℂ)
    (K : ι → Config n → Config n → Config n → Config n → ℂ) :
    twoCopyForm Φ (fun x y x' y' => ∑ t ∈ s, K t x y x' y') =
      ∑ t ∈ s, twoCopyForm Φ (K t) := by
  unfold twoCopyForm
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := s) (t := (Finset.univ : Finset (Config n)))]

private lemma twoCopyForm_const_mul (Φ : Config n → Config n → ℂ) (c : ℂ)
    (K : Config n → Config n → Config n → Config n → ℂ) :
    twoCopyForm Φ (fun x y x' y' => c * K x y x' y') = c * twoCopyForm Φ K := by
  unfold twoCopyForm
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

private lemma twoCopyForm_two_mul_sub (Φ : Config n → Config n → ℂ)
    (A B : Config n → Config n → Config n → Config n → ℂ) :
    twoCopyForm Φ (fun x y x' y' => 2 * A x y x' y' - B x y x' y') =
      2 * twoCopyForm Φ A - twoCopyForm Φ B := by
  unfold twoCopyForm
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

/-- The form of a rank-one integer kernel `A ⊗ A` is `|∑ A Φ|² ≥ 0`. -/
private lemma twoCopyForm_rank_one_nonneg (Φ : Config n → Config n → ℂ)
    (A : Config n → Config n → ℤ) :
    0 ≤ (twoCopyForm Φ (fun x y x' y' => ((A x y * A x' y' : ℤ) : ℂ))).re := by
  have h : twoCopyForm Φ (fun x y x' y' => ((A x y * A x' y' : ℤ) : ℂ)) =
      star (∑ x, ∑ y, (A x y : ℂ) * Φ x y) * ∑ x, ∑ y, (A x y : ℂ) * Φ x y := by
    unfold twoCopyForm
    simp only [star_sum, star_mul', star_intCast]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
    push_cast
    ring
  rw [h, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- Positivity of the form of a product kernel whose local factors are integer Gram matrices
(with five Gram vectors each). -/
private lemma twoCopyForm_gram_nonneg (k : Fin n → Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℤ)
    (v : Fin n → Fin 5 → Fin 2 × Fin 2 → ℤ)
    (hk : ∀ l p p', k l p p' = ∑ τ, v l τ p * v l τ p') (Φ : Config n → Config n → ℂ) :
    0 ≤ (twoCopyForm Φ
      (fun x y x' y' => ((∏ l, k l (x l, y l) (x' l, y' l) : ℤ) : ℂ))).re := by
  have hK : (fun x y x' y' : Config n => ((∏ l, k l (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      fun x y x' y' : Config n => ∑ τ : Fin n → Fin 5,
        (((∏ l, v l (τ l) (x l, y l)) * (∏ l, v l (τ l) (x' l, y' l)) : ℤ) : ℂ) := by
    funext x y x' y'
    simp only [hk]
    rw [Fintype.prod_sum]
    push_cast
    simp only [Finset.prod_mul_distrib]
  rw [hK, twoCopyForm_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun τ _ =>
    twoCopyForm_rank_one_nonneg Φ (fun x y => ∏ l, v l (τ l) (x l, y l))

/-- The form of the kernel `[(x', y') = (f x y, g x y)]`. -/
private lemma twoCopyForm_ind_left (Φ : Config n → Config n → ℂ)
    (f g : Config n → Config n → Config n) :
    twoCopyForm Φ (fun x y x' y' => if x' = f x y ∧ y' = g x y then 1 else 0) =
      ∑ x, ∑ y, star (Φ x y) * Φ (f x y) (g x y) := by
  unfold twoCopyForm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_eq_single (f x y), Fintype.sum_eq_single (g x y)]
  · simp
  · intro y' hy'
    simp [hy']
  · intro x' hx'
    simp [hx']

/-- The form of the kernel `[(y, x') = (f x y', g x y')]`. -/
private lemma twoCopyForm_ind_cross (Φ : Config n → Config n → ℂ)
    (f g : Config n → Config n → Config n) :
    twoCopyForm Φ (fun x y x' y' => if y = f x y' ∧ x' = g x y' then 1 else 0) =
      ∑ x, ∑ y', star (Φ x (f x y')) * Φ (g x y') y' := by
  unfold twoCopyForm
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Fintype.sum_eq_single (f x y'), Fintype.sum_eq_single (g x y')]
  · simp
  · intro x' hx'
    simp [hx']
  · intro y hy
    simp [hy]

/- Local kernels and their Gram vectors -/

/-- A function on pairs, given by its values at `00, 01, 10, 11`. -/
private def pairVec (a b c d : ℤ) (p : Fin 2 × Fin 2) : ℤ :=
  if p.1 = 0 then (if p.2 = 0 then a else b) else (if p.2 = 0 then c else d)

/-- The local shadow kernel `I + e • SWAP`. -/
private def swapKer (e : ℤ) (p p' : Fin 2 × Fin 2) : ℤ :=
  (if p' = p then 1 else 0) + e * (if p' = (p.2, p.1) then 1 else 0)

/-- Gram vectors of `I + SWAP`. -/
private def swapVecPlus : Fin 5 → Fin 2 × Fin 2 → ℤ :=
  ![pairVec 1 0 0 0, pairVec 1 0 0 0, pairVec 0 0 0 1, pairVec 0 0 0 1, pairVec 0 1 1 0]

/-- Gram vectors of `I - SWAP`. -/
private def swapVecMinus : Fin 5 → Fin 2 × Fin 2 → ℤ :=
  ![pairVec 0 1 (-1) 0, pairVec 0 0 0 0, pairVec 0 0 0 0, pairVec 0 0 0 0, pairVec 0 0 0 0]

private lemma swapKer_one_gram :
    ∀ p p' : Fin 2 × Fin 2, swapKer 1 p p' = ∑ τ, swapVecPlus τ p * swapVecPlus τ p' := by
  decide

private lemma swapKer_neg_one_gram :
    ∀ p p' : Fin 2 × Fin 2, swapKer (-1) p p' = ∑ τ, swapVecMinus τ p * swapVecMinus τ p' := by
  decide

/-- The identity kernel on pairs. -/
private def idKer (p p' : Fin 2 × Fin 2) : ℤ := if p' = p then 1 else 0

/-- The kernel `e eᵀ`, where `e (a, b) = [a = b]`. -/
private def diagKer (p p' : Fin 2 × Fin 2) : ℤ := if p.1 = p.2 ∧ p'.1 = p'.2 then 1 else 0

/-- The kernel `2 I - e eᵀ`. -/
private def twoIdSubDiagKer (p p' : Fin 2 × Fin 2) : ℤ := 2 * idKer p p' - diagKer p p'

/-- Gram vectors of the identity. -/
private def idVec : Fin 5 → Fin 2 × Fin 2 → ℤ :=
  ![pairVec 1 0 0 0, pairVec 0 1 0 0, pairVec 0 0 1 0, pairVec 0 0 0 1, pairVec 0 0 0 0]

/-- Gram vectors of `e eᵀ`. -/
private def diagVec : Fin 5 → Fin 2 × Fin 2 → ℤ :=
  ![pairVec 1 0 0 1, pairVec 0 0 0 0, pairVec 0 0 0 0, pairVec 0 0 0 0, pairVec 0 0 0 0]

/-- Gram vectors of `2 I - e eᵀ`. -/
private def twoIdSubDiagVec : Fin 5 → Fin 2 × Fin 2 → ℤ :=
  ![pairVec 1 0 0 (-1), pairVec 0 1 0 0, pairVec 0 1 0 0, pairVec 0 0 1 0, pairVec 0 0 1 0]

private lemma idKer_gram :
    ∀ p p' : Fin 2 × Fin 2, idKer p p' = ∑ τ, idVec τ p * idVec τ p' := by
  decide

private lemma diagKer_gram :
    ∀ p p' : Fin 2 × Fin 2, diagKer p p' = ∑ τ, diagVec τ p * diagVec τ p' := by
  decide

private lemma twoIdSubDiagKer_gram :
    ∀ p p' : Fin 2 × Fin 2,
      twoIdSubDiagKer p p' = ∑ τ, twoIdSubDiagVec τ p * twoIdSubDiagVec τ p' := by
  decide

private lemma idKer_mk :
    ∀ a b a' b' : Fin 2, idKer (a, b) (a', b') = if b = b' ∧ a' = a then 1 else 0 := by
  decide

private lemma diagKer_mk :
    ∀ a b a' b' : Fin 2, diagKer (a, b) (a', b') = if b = a ∧ a' = b' then 1 else 0 := by
  decide

/- The shadow inequality -/

/-- The sign `η l`: `1` at the site `i`, `-1` elsewhere. -/
private def siteSign (i l : Fin n) : ℤ := if l = i then 1 else -1

/-- Expanding the product of the local shadow kernels over the sites. -/
private lemma prod_swapKer (i : Fin n) (x y x' y' : Config n) :
    ∏ l, swapKer (siteSign i l) (x l, y l) (x' l, y' l) =
      ∑ T : Finset (Fin n), (∏ l ∈ T, siteSign i l) *
        (if x' = mix T x y ∧ y' = mix T y x then 1 else 0) := by
  have h1 : ∀ l, swapKer (siteSign i l) (x l, y l) (x' l, y' l) =
      siteSign i l * (if (x' l, y' l) = (y l, x l) then 1 else 0) +
        (if (x' l, y' l) = (x l, y l) then 1 else 0) := fun l => by
    unfold swapKer
    ring
  simp only [h1]
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  have hC : (if x' = mix T x y ∧ y' = mix T y x then (1 : ℤ) else 0) =
      ∏ l, if x' l = mix T x y l ∧ y' l = mix T y x l then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff, forall_and]
  rw [hC, ← Finset.prod_mul_prod_compl T]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [hl]
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [Finset.mem_compl] at hl
    simp [hl]

private lemma twoCopyForm_swapKer (ψ : Config n → ℂ) (i : Fin n) :
    twoCopyForm (fun x y => star (ψ x) * star (ψ y))
      (fun x y x' y' => ((∏ l, swapKer (siteSign i l) (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      ∑ T : Finset (Fin n), ((∏ l ∈ T, siteSign i l : ℤ) : ℂ) * purC ψ T := by
  simp only [prod_swapKer]
  push_cast
  rw [twoCopyForm_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [twoCopyForm_const_mul, twoCopyForm_ind_left]
  unfold purC
  simp only [star_mul', star_star, mul_assoc]

theorem shadow_nonneg (ψ : Config n → ℂ) (i : Fin n) :
    0 ≤ ∑ T : Finset (Fin n), (∏ l ∈ T, (if l = i then (1 : ℝ) else -1)) * pur ψ T := by
  have hk : ∀ l p p', swapKer (siteSign i l) p p' =
      ∑ τ, (if l = i then swapVecPlus else swapVecMinus) τ p *
        (if l = i then swapVecPlus else swapVecMinus) τ p' := by
    intro l p p'
    by_cases h : l = i
    · subst h
      simpa [siteSign] using swapKer_one_gram p p'
    · simpa [siteSign, h] using swapKer_neg_one_gram p p'
  have h := twoCopyForm_gram_nonneg _ _ hk (fun x y => star (ψ x) * star (ψ y))
  rw [twoCopyForm_swapKer, Complex.re_sum] at h
  refine h.trans_eq (Finset.sum_congr rfl fun T _ => ?_)
  rw [pur, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
  push_cast [siteSign]
  rfl

/- The shadow inequality for an arbitrary set of `+` sites -/

/-- The sign `η l`: `1` on `E`, `-1` elsewhere. -/
private def setSign (E : Finset (Fin n)) (l : Fin n) : ℤ := if l ∈ E then 1 else -1

/-- Expanding the product of the local shadow kernels over the sites. -/
private lemma prod_swapKer_set (E : Finset (Fin n)) (x y x' y' : Config n) :
    ∏ l, swapKer (setSign E l) (x l, y l) (x' l, y' l) =
      ∑ T : Finset (Fin n), (∏ l ∈ T, setSign E l) *
        (if x' = mix T x y ∧ y' = mix T y x then 1 else 0) := by
  have h1 : ∀ l, swapKer (setSign E l) (x l, y l) (x' l, y' l) =
      setSign E l * (if (x' l, y' l) = (y l, x l) then 1 else 0) +
        (if (x' l, y' l) = (x l, y l) then 1 else 0) := fun l => by
    unfold swapKer
    ring
  simp only [h1]
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  have hC : (if x' = mix T x y ∧ y' = mix T y x then (1 : ℤ) else 0) =
      ∏ l, if x' l = mix T x y l ∧ y' l = mix T y x l then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff, forall_and]
  rw [hC, ← Finset.prod_mul_prod_compl T]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [hl]
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [Finset.mem_compl] at hl
    simp [hl]

private lemma twoCopyForm_swapKer_set (ψ : Config n → ℂ) (E : Finset (Fin n)) :
    twoCopyForm (fun x y => star (ψ x) * star (ψ y))
      (fun x y x' y' => ((∏ l, swapKer (setSign E l) (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      ∑ T : Finset (Fin n), ((∏ l ∈ T, setSign E l : ℤ) : ℂ) * purC ψ T := by
  simp only [prod_swapKer_set]
  push_cast
  rw [twoCopyForm_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [twoCopyForm_const_mul, twoCopyForm_ind_left]
  unfold purC
  simp only [star_mul', star_star, mul_assoc]

/-- The shadow inequality `S_E ≥ 0` for an arbitrary set `E` of sites. -/
theorem shadow_nonneg_set (ψ : Config n → ℂ) (E : Finset (Fin n)) :
    0 ≤ ∑ T : Finset (Fin n), (∏ l ∈ T, (if l ∈ E then (1 : ℝ) else -1)) * pur ψ T := by
  have hk : ∀ l p p', swapKer (setSign E l) p p' =
      ∑ τ, (if l ∈ E then swapVecPlus else swapVecMinus) τ p *
        (if l ∈ E then swapVecPlus else swapVecMinus) τ p' := by
    intro l p p'
    by_cases h : l ∈ E
    · simpa [setSign, h] using swapKer_one_gram p p'
    · simpa [setSign, h] using swapKer_neg_one_gram p p'
  have h := twoCopyForm_gram_nonneg _ _ hk (fun x y => star (ψ x) * star (ψ y))
  rw [twoCopyForm_swapKer_set, Complex.re_sum] at h
  refine h.trans_eq (Finset.sum_congr rfl fun T _ => ?_)
  rw [pur, ← Complex.ofReal_intCast, Complex.re_ofReal_mul]
  push_cast [setSign]
  rfl

/- The local purity bound -/

/-- The local purity kernel: the identity on `T`, and `e eᵀ` off `T`. -/
private def purKer (T : Finset (Fin n)) (l : Fin n) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℤ :=
  if l ∈ T then idKer else diagKer

private lemma prod_purKer (T : Finset (Fin n)) (x y x' y' : Config n) :
    ∏ l, purKer T l (x l, y l) (x' l, y' l) =
      if y = mix T x y' ∧ x' = mix T y' x then 1 else 0 := by
  have h1 : ∀ l, purKer T l (x l, y l) (x' l, y' l) =
      if y l = mix T x y' l ∧ x' l = mix T y' x l then 1 else 0 := fun l => by
    by_cases hl : l ∈ T
    · simp only [purKer, hl, ite_true, mix_apply]
      exact idKer_mk _ _ _ _
    · simp only [purKer, hl, ite_false, mix_apply]
      exact diagKer_mk _ _ _ _
  simp only [h1, Fintype.prod_boole]
  simp only [funext_iff, forall_and]

private lemma two_mul_prod_purKer_insert_sub (W : Finset (Fin n)) (i : Fin n) (hi : i ∉ W)
    (x y x' y' : Config n) :
    2 * ∏ l, purKer (insert i W) l (x l, y l) (x' l, y' l) -
        ∏ l, purKer W l (x l, y l) (x' l, y' l) =
      ∏ l, (if l = i then twoIdSubDiagKer else purKer W l) (x l, y l) (x' l, y' l) := by
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i]
  have h1 : purKer (insert i W) i = idKer := by simp [purKer]
  have h2 : purKer W i = diagKer := by simp [purKer, hi]
  have h3 : ∏ l ∈ {i}ᶜ, purKer (insert i W) l (x l, y l) (x' l, y' l) =
      ∏ l ∈ {i}ᶜ, purKer W l (x l, y l) (x' l, y' l) := Finset.prod_congr rfl fun l hl => by
    have hli : l ≠ i := by simpa using hl
    simp [purKer, Finset.mem_insert, hli]
  have h4 : ∏ l ∈ {i}ᶜ, (if l = i then twoIdSubDiagKer else purKer W l) (x l, y l) (x' l, y' l) =
      ∏ l ∈ {i}ᶜ, purKer W l (x l, y l) (x' l, y' l) := Finset.prod_congr rfl fun l hl => by
    have hli : l ≠ i := by simpa using hl
    simp [hli]
  rw [h1, h2, h3, h4]
  simp only [ite_true]
  unfold twoIdSubDiagKer
  ring

private lemma twoCopyForm_purKer (ψ : Config n → ℂ) (T : Finset (Fin n)) :
    twoCopyForm (fun x y => ψ x * star (ψ y))
      (fun x y x' y' => ((∏ l, purKer T l (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      star (purC ψ T) := by
  simp only [prod_purKer]
  push_cast
  rw [twoCopyForm_ind_cross]
  unfold purC
  simp only [star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem pur_le_two_mul_pur_insert (ψ : Config n → ℂ) (W : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ W) : pur ψ W ≤ 2 * pur ψ (insert i W) := by
  have hk : ∀ l p p', (if l = i then twoIdSubDiagKer else purKer W l) p p' =
      ∑ τ, (if l = i then twoIdSubDiagVec else if l ∈ W then idVec else diagVec) τ p *
        (if l = i then twoIdSubDiagVec else if l ∈ W then idVec else diagVec) τ p' := by
    intro l p p'
    by_cases h : l = i
    · subst h
      simpa using twoIdSubDiagKer_gram p p'
    · by_cases hW : l ∈ W
      · simpa [h, hW, purKer] using idKer_gram p p'
      · simpa [h, hW, purKer] using diagKer_gram p p'
  have h := twoCopyForm_gram_nonneg _ _ hk (fun x y => ψ x * star (ψ y))
  have hK : (fun x y x' y' : Config n =>
      ((∏ l, (if l = i then twoIdSubDiagKer else purKer W l) (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      fun x y x' y' : Config n =>
        2 * ((∏ l, purKer (insert i W) l (x l, y l) (x' l, y' l) : ℤ) : ℂ) -
          ((∏ l, purKer W l (x l, y l) (x' l, y' l) : ℤ) : ℂ) := by
    funext x y x' y'
    rw [← two_mul_prod_purKer_insert_sub W i hi]
    push_cast
    ring
  rw [hK, twoCopyForm_two_mul_sub, twoCopyForm_purKer, twoCopyForm_purKer] at h
  have e : ∀ z : ℂ, (star z).re = z.re := fun z => by simp
  simp only [Complex.sub_re, Complex.mul_re, e] at h
  simp only [pur]
  norm_num at h
  linarith

/- Subsystem shadow inequalities -/

/-- `swapKer 0` is the identity kernel. -/
private lemma swapKer_zero_gram :
    ∀ p p' : Fin 2 × Fin 2, swapKer 0 p p' = ∑ τ, idVec τ p * idVec τ p' := by
  decide

/-- Expanding a product of local shadow kernels with arbitrary integer signs. -/
private lemma prod_swapKer_gen (η : Fin n → ℤ) (x y x' y' : Config n) :
    ∏ l, swapKer (η l) (x l, y l) (x' l, y' l) =
      ∑ T : Finset (Fin n), (∏ l ∈ T, η l) *
        (if x' = mix T x y ∧ y' = mix T y x then 1 else 0) := by
  have h1 : ∀ l, swapKer (η l) (x l, y l) (x' l, y' l) =
      η l * (if (x' l, y' l) = (y l, x l) then 1 else 0) +
        (if (x' l, y' l) = (x l, y l) then 1 else 0) := fun l => by
    unfold swapKer
    ring
  simp only [h1]
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  have hC : (if x' = mix T x y ∧ y' = mix T y x then (1 : ℤ) else 0) =
      ∏ l, if x' l = mix T x y l ∧ y' l = mix T y x l then 1 else 0 := by
    rw [Fintype.prod_boole]
    simp only [funext_iff, forall_and]
  rw [hC, ← Finset.prod_mul_prod_compl T]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [hl]
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [Finset.mem_compl] at hl
    simp [hl]

private lemma twoCopyForm_swapKer_gen (ψ : Config n → ℂ) (η : Fin n → ℤ) :
    twoCopyForm (fun x y => star (ψ x) * star (ψ y))
      (fun x y x' y' => ((∏ l, swapKer (η l) (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      ∑ T : Finset (Fin n), ((∏ l ∈ T, η l : ℤ) : ℂ) * purC ψ T := by
  simp only [prod_swapKer_gen]
  push_cast
  rw [twoCopyForm_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [twoCopyForm_const_mul, twoCopyForm_ind_left]
  unfold purC
  simp only [star_mul', star_star, mul_assoc]

/-- The sign `-1` on `S` and `0` (the identity kernel) off `S`. -/
private def subSign (S : Finset (Fin n)) (l : Fin n) : ℤ := if l ∈ S then -1 else 0

private lemma prod_subSign (S T : Finset (Fin n)) :
    ∏ l ∈ T, subSign S l = if T ⊆ S then (-1) ^ T.card else 0 := by
  split_ifs with h
  · rw [Finset.prod_congr rfl fun l hl => show subSign S l = -1 by simp [subSign, h hl],
      Finset.prod_const]
  · obtain ⟨l, hlT, hlS⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hlT (by simp [subSign, hlS])

/-- The shadow inequality of the reduced state on `S`: `∑_{T ⊆ S} (-1)^|T| Tr ρ_T² ≥ 0`. -/
theorem subsystem_shadow_nonneg (ψ : Config n → ℂ) (S : Finset (Fin n)) :
    0 ≤ ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * pur ψ T := by
  have hk : ∀ l p p', swapKer (subSign S l) p p' =
      ∑ τ, (if l ∈ S then swapVecMinus else idVec) τ p *
        (if l ∈ S then swapVecMinus else idVec) τ p' := by
    intro l p p'
    by_cases h : l ∈ S
    · simpa [subSign, h] using swapKer_neg_one_gram p p'
    · simpa [subSign, h] using swapKer_zero_gram p p'
  have h := twoCopyForm_gram_nonneg _ _ hk (fun x y => star (ψ x) * star (ψ y))
  rw [twoCopyForm_swapKer_gen, Complex.re_sum] at h
  have hT : ∀ T : Finset (Fin n),
      (((∏ l ∈ T, subSign S l : ℤ) : ℂ) * purC ψ T).re =
        if T ⊆ S then (-1 : ℝ) ^ T.card * pur ψ T else 0 := by
    intro T
    rw [prod_subSign]
    split_ifs
    · push_cast
      rw [show ((-1 : ℂ) ^ T.card) = (((-1 : ℝ) ^ T.card : ℝ) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
      rfl
    · simp
  simp only [hT] at h
  rw [← Finset.sum_filter] at h
  have hpow : (Finset.univ.filter fun T : Finset (Fin n) => T ⊆ S) = S.powerset := by
    ext T
    simp
  rwa [hpow] at h

/- Nonnegativity of the Möbius (Pauli-sector) coefficients -/

/-- The kernel `2 I - e eᵀ` on `R` and `e eᵀ` off `R`. -/
private def mobKer (R : Finset (Fin n)) (l : Fin n) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℤ :=
  if l ∈ R then twoIdSubDiagKer else diagKer

private lemma prod_mobKer (R : Finset (Fin n)) (x y x' y' : Config n) :
    ∏ l, mobKer R l (x l, y l) (x' l, y' l) =
      ∑ U ∈ R.powerset, (2 ^ U.card * (-1) ^ (R.card - U.card)) *
        ∏ l, purKer U l (x l, y l) (x' l, y' l) := by
  set I : Fin n → ℤ := fun l => idKer (x l, y l) (x' l, y' l) with hI
  set E : Fin n → ℤ := fun l => diagKer (x l, y l) (x' l, y' l) with hE
  have hsplit : ∏ l, mobKer R l (x l, y l) (x' l, y' l) =
      (∏ l ∈ R, (2 * I l + -E l)) * ∏ l ∈ Rᶜ, E l := by
    rw [← Finset.prod_mul_prod_compl R]
    congr 1
    · refine Finset.prod_congr rfl fun l hl => ?_
      simp [mobKer, hl, twoIdSubDiagKer, hI, hE, sub_eq_add_neg]
    · refine Finset.prod_congr rfl fun l hl => ?_
      rw [Finset.mem_compl] at hl
      simp [mobKer, hl, hE]
  rw [hsplit, Finset.prod_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [Finset.mem_powerset] at hU
  have hpur : ∏ l, purKer U l (x l, y l) (x' l, y' l) =
      (∏ l ∈ U, I l) * ((∏ l ∈ R \ U, E l) * ∏ l ∈ Rᶜ, E l) := by
    rw [← Finset.prod_mul_prod_compl U]
    congr 1
    · refine Finset.prod_congr rfl fun l hl => ?_
      simp [purKer, hl, hI]
    · have hdisj : Disjoint (R \ U) Rᶜ := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        exact (Finset.mem_compl.mp hl') (Finset.mem_sdiff.mp hl).1
      have hUc : Uᶜ = (R \ U) ∪ Rᶜ := by
        ext l
        by_cases hlU : l ∈ U
        · have hlR : l ∈ R := hU hlU
          simp [hlU, hlR]
        · by_cases hlR : l ∈ R <;> simp [hlU, hlR]
      rw [hUc, Finset.prod_union hdisj]
      congr 1
      · refine Finset.prod_congr rfl fun l hl => ?_
        simp [purKer, (Finset.mem_sdiff.mp hl).2, hE]
      · refine Finset.prod_congr rfl fun l hl => ?_
        have hlU : l ∉ U := fun h => (Finset.mem_compl.mp hl) (hU h)
        simp [purKer, hlU, hE]
  rw [hpur, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_neg,
    Finset.card_sdiff_of_subset hU]
  ring

/-- The Möbius coefficient `∑_{U ⊆ R} (-1)^{|R \ U|} 2^|U| Tr ρ_U²` is nonnegative: it is
`2^|R|` times the total squared weight of the Pauli strings with support exactly `R`. -/
theorem moebius_nonneg (ψ : Config n → ℂ) (R : Finset (Fin n)) :
    0 ≤ ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * 2 ^ U.card * pur ψ U := by
  have hk : ∀ l p p', mobKer R l p p' =
      ∑ τ, (if l ∈ R then twoIdSubDiagVec else diagVec) τ p *
        (if l ∈ R then twoIdSubDiagVec else diagVec) τ p' := by
    intro l p p'
    by_cases h : l ∈ R
    · simpa [mobKer, h] using twoIdSubDiagKer_gram p p'
    · simpa [mobKer, h] using diagKer_gram p p'
  have h := twoCopyForm_gram_nonneg _ _ hk (fun x y => ψ x * star (ψ y))
  have hK : (fun x y x' y' : Config n =>
      ((∏ l, mobKer R l (x l, y l) (x' l, y' l) : ℤ) : ℂ)) =
      fun x y x' y' : Config n => ∑ U ∈ R.powerset,
        ((2 ^ U.card * (-1) ^ (R.card - U.card) : ℤ) : ℂ) *
          ((∏ l, purKer U l (x l, y l) (x' l, y' l) : ℤ) : ℂ) := by
    funext x y x' y'
    rw [prod_mobKer]
    push_cast
    rfl
  rw [hK, twoCopyForm_sum, Complex.re_sum] at h
  refine h.trans_eq (Finset.sum_congr rfl fun U _ => ?_)
  rw [twoCopyForm_const_mul, twoCopyForm_purKer]
  have e : ((2 ^ U.card * (-1) ^ (R.card - U.card) : ℤ) : ℂ) =
      (((2 : ℝ) ^ U.card * (-1) ^ (R.card - U.card) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e, Complex.re_ofReal_mul]
  simp only [pur, Complex.star_def, Complex.conj_re]
  ring

end QuantumExtremalNumber
