import Qex94.PurityFacts

/-!
# The combinatorial core for ten qubits

A real function `p` on subsets of ten qubits with the purity axioms allows at most `208`
five-sets with minimal purity `1/32`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.Abstract10

open PurityFacts

/-- At most 43 bad five-sets force `p U = (1/2)^|U|` for every `U` with `|U| ≤ 2`. -/
lemma uniform_of_few_bad (p : Finset (Fin 10) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 10) (W : Finset (Fin 10)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : ((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32)).card
      ≤ 43)
    (U : Finset (Fin 10)) (hU : U.card ≤ 2) : p U = (1 / 2 : ℝ) ^ U.card := by
  have hex : ∃ S ∈ powersetCard 5 (univ : Finset (Fin 10)), U ⊆ S ∧ p S = 1 / 32 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hsub : (powersetCard 5 (univ : Finset (Fin 10))).filter (fun S => U ⊆ S) ⊆
        (powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32) := by
      intro S hS
      rw [mem_filter] at hS ⊢
      exact ⟨hS.1, hne S hS.1 hS.2⟩
    have h1 := card_le_card hsub
    have h2 := choose_le_card_supersets 5 U (by omega)
    have h3 : 44 ≤ Nat.choose (10 - U.card) (5 - U.card) := by
      obtain h | h | h : U.card = 0 ∨ U.card = 1 ∨ U.card = 2 := by omega
      all_goals rw [h]; decide
    omega
  obtain ⟨S, hS, hUS, hpS⟩ := hex
  apply eq_half_pow_of_subset p h0 hloc U S hUS
  rw [hpS, (mem_powersetCard.1 hS).2]
  norm_num

/-- The lower bound `15 ≤ P p 3`. -/
lemma P_three_ge (p : Finset (Fin 10) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 10) (W : Finset (Fin 10)), i ∉ W → p W ≤ 2 * p (insert i W)) :
    15 ≤ P p 3 := by
  have h : ∀ T ∈ powersetCard 3 (univ : Finset (Fin 10)), (1 / 8 : ℝ) ≤ p T := by
    intro T hT
    have := half_pow_le p h0 hloc T
    rw [(mem_powersetCard.1 hT).2] at this
    norm_num at this
    exact this
  have hsum := sum_le_sum h
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h120 : Nat.choose 10 3 = 120 := by decide
  rw [h120] at hsum
  unfold P
  norm_num at hsum
  linarith

/-- The shadow inequality, once the first three level sums are known. -/
lemma shadow_ineq (p : Finset (Fin 10) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hshadow : 0 ≤ ∑ T : Finset (Fin 10),
      (-1 : ℝ) ^ T.card * (((T.card : ℝ) - 4) * ((T.card : ℝ) - 6)) * p T)
    (h1 : P p 1 = 5) (h2 : P p 2 = 45 / 4) : 0 ≤ 78 - 6 * P p 3 + P p 5 := by
  rw [sum_eq_sum_P p (fun k => (-1 : ℝ) ^ k * (((k : ℝ) - 4) * ((k : ℝ) - 6)))] at hshadow
  simp only [sum_range_succ, sum_range_zero] at hshadow
  norm_num at hshadow
  have e0 : P p 0 = 1 := by
    unfold P; rw [powersetCard_zero, sum_singleton, h0]
  have c10 := P_compl p hcompl 0 10 rfl
  have c9 := P_compl p hcompl 1 9 rfl
  have c8 := P_compl p hcompl 2 8 rfl
  have c7 := P_compl p hcompl 3 7 rfl
  have c6 := P_compl p hcompl 4 6 rfl
  linarith

/-- There are `25` sets `insert x (S.erase i)` with `i ∈ S` and `x ∉ S`. -/
lemma card_image_swap (S : Finset (Fin 10)) (hS : S.card = 5) :
    ((S ×ˢ Sᶜ).image (fun q : Fin 10 × Fin 10 => insert q.2 (S.erase q.1))).card = 25 := by
  rw [card_image_of_injOn, card_product, card_compl, Fintype.card_fin, hS]
  rintro ⟨i, x⟩ hix ⟨j, y⟩ hjy h
  simp only [coe_product, Set.mem_prod, mem_coe, mem_compl] at hix hjy
  simp only at h
  have hx : x = y := by
    have hxy : x ∈ insert y (S.erase j) := h ▸ mem_insert_self x _
    rw [mem_insert] at hxy
    rcases hxy with h' | h'
    · exact h'
    · exact absurd (mem_of_mem_erase h') hix.2
  subst hx
  have hi : i = j := by
    by_contra hij
    have hi' : i ∈ insert x (S.erase j) := mem_insert_of_mem (mem_erase.2 ⟨hij, hix.1⟩)
    rw [← h, mem_insert, mem_erase] at hi'
    rcases hi' with h' | h'
    · exact hix.2 (h' ▸ hix.1)
    · exact h'.1 rfl
  rw [hi]

/-- No set `insert x (S.erase i)` is the complement of another such set. -/
lemma disjoint_image_compl (S : Finset (Fin 10)) (hS : S.card = 5) :
    Disjoint ((S ×ˢ Sᶜ).image (fun q : Fin 10 × Fin 10 => insert q.2 (S.erase q.1)))
      (((S ×ˢ Sᶜ).image (fun q : Fin 10 × Fin 10 => insert q.2 (S.erase q.1))).image
        compl) := by
  rw [disjoint_left]
  intro T hT hT'
  simp only [mem_image, mem_product, mem_compl, Prod.exists] at hT hT'
  obtain ⟨i, x, ⟨hi, hx⟩, rfl⟩ := hT
  obtain ⟨U, ⟨j, y, ⟨hj, hy⟩, rfl⟩, hU⟩ := hT'
  have hc : 0 < ((S.erase i).erase j).card := by
    have e1 := pred_card_le_card_erase (s := S) (a := i)
    have e2 := pred_card_le_card_erase (s := S.erase i) (a := j)
    omega
  obtain ⟨k, hk⟩ := card_pos.1 hc
  rw [mem_erase, mem_erase] at hk
  have hk' : k ∈ insert x (S.erase i) := mem_insert_of_mem (mem_erase.2 ⟨hk.2.1, hk.2.2⟩)
  rw [← hU, mem_compl] at hk'
  exact hk' (mem_insert_of_mem (mem_erase.2 ⟨hk.1, hk.2.2⟩))

/-- If at most 43 five-sets are bad, every five-set has a four-subset of minimal purity. -/
lemma exists_good_erase (p : Finset (Fin 10) → ℝ) (h0 : p ∅ = 1)
    (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 10) (W : Finset (Fin 10)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : ((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32)).card
      ≤ 43)
    (S : Finset (Fin 10)) (hS : S.card = 5) : ∃ i ∈ S, p (S.erase i) = 1 / 16 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  set A := (S ×ˢ Sᶜ).image (fun q : Fin 10 × Fin 10 => insert q.2 (S.erase q.1)) with hA
  set B := (powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32)
    with hBdef
  have hAB : A ⊆ B := by
    intro T hT
    rw [hA] at hT
    simp only [mem_image, mem_product, mem_compl, Prod.exists] at hT
    obtain ⟨i, x, ⟨hi, hx⟩, rfl⟩ := hT
    have hx' : x ∉ S.erase i := fun h => hx (mem_of_mem_erase h)
    have hcard : (insert x (S.erase i)).card = 5 := by
      rw [card_insert_of_notMem hx', card_erase_of_mem hi, hS]
    rw [hBdef, mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, hcard⟩, fun hpT => hne i hi ?_⟩
    have := eq_half_pow_of_subset p h0 hloc (S.erase i) (insert x (S.erase i))
      (subset_insert _ _) (by rw [hpT, hcard]; norm_num)
    rw [this, card_erase_of_mem hi, hS]
    norm_num
  have hA'B : A.image compl ⊆ B := by
    intro T hT
    simp only [mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    have hU' := hAB hU
    rw [hBdef, mem_filter, mem_powersetCard] at hU' ⊢
    refine ⟨⟨subset_univ _, ?_⟩, ?_⟩
    · rw [card_compl, Fintype.card_fin, hU'.1.2]
    · rw [hcompl]
      exact hU'.2
  have hcard : (A ∪ A.image compl).card = 50 := by
    rw [card_union_of_disjoint (disjoint_image_compl S hS),
      card_image_of_injective _ compl_injective, card_image_swap S hS]
  have := card_le_card (union_subset hAB hA'B)
  omega

/-- Upper bound for `P p 5` in terms of the numbers of good and bad five-sets. -/
lemma P_five_le (p : Finset (Fin 10) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 10) (W : Finset (Fin 10)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : ((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32)).card
      ≤ 43) :
    32 * P p 5 ≤
      (((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => p A = 1 / 32)).card : ℝ) +
      4 * (((powersetCard 5 (univ : Finset (Fin 10))).filter
        (fun A => ¬ p A = 1 / 32)).card : ℝ) := by
  unfold P
  rw [← sum_filter_add_sum_filter_not (powersetCard 5 univ) (fun A => p A = 1 / 32)]
  have hG : ∑ S ∈ (powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => p A = 1 / 32),
      p S = (((powersetCard 5 (univ : Finset (Fin 10))).filter
        (fun A => p A = 1 / 32)).card : ℝ) * (1 / 32) := by
    rw [sum_congr rfl (fun S hS => (mem_filter.1 hS).2), sum_const, nsmul_eq_mul]
  have hBle : ∑ S ∈ (powersetCard 5 (univ : Finset (Fin 10))).filter
      (fun A => ¬ p A = 1 / 32), p S ≤
      ∑ S ∈ (powersetCard 5 (univ : Finset (Fin 10))).filter
      (fun A => ¬ p A = 1 / 32), (1 / 8 : ℝ) := by
    apply sum_le_sum
    intro S hS
    have hS5 : S.card = 5 := (mem_powersetCard.1 (mem_filter.1 hS).1).2
    obtain ⟨i, hi, hpi⟩ := exists_good_erase p h0 hcompl hloc hB S hS5
    have := up_le p hcompl hloc i (S.erase i) (notMem_erase i S)
    rw [insert_erase hi, hpi] at this
    linarith
  rw [sum_const, nsmul_eq_mul] at hBle
  linarith

theorem abstract_bound_ten (p : Finset (Fin 10) → ℝ)
    (h0 : p ∅ = 1)
    (hcompl : ∀ T, p Tᶜ = p T)
    (hshadow : 0 ≤ ∑ T : Finset (Fin 10),
      (-1 : ℝ) ^ T.card * (((T.card : ℝ) - 4) * ((T.card : ℝ) - 6)) * p T)
    (hloc : ∀ (i : Fin 10) (W : Finset (Fin 10)), i ∉ W → p W ≤ 2 * p (insert i W)) :
    ((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => p A = 1 / 32)).card ≤ 208 := by
  by_contra hcon
  rw [not_le] at hcon
  -- at most `252 - 209 = 43` five-sets are bad
  have htot := card_filter_add_card_filter_not (s := powersetCard 5 (univ : Finset (Fin 10)))
    (fun A => p A = 1 / 32)
  rw [card_powersetCard, card_univ, Fintype.card_fin] at htot
  have h252 : Nat.choose 10 5 = 252 := by decide
  rw [h252] at htot
  have hB : ((powersetCard 5 (univ : Finset (Fin 10))).filter (fun A => ¬ p A = 1 / 32)).card
      ≤ 43 := by omega
  -- hence `p` is 2-uniform, which pins down `P p 1` and `P p 2`
  have huni := uniform_of_few_bad p h0 hloc hB
  have h1 : P p 1 = 5 := by
    rw [P_const p 1 (1 / 2) (fun U hU => by rw [huni U (by omega), hU]; norm_num)]
    norm_num
  have h2 : P p 2 = 45 / 4 := by
    rw [P_const p 2 (1 / 4) (fun U hU => by rw [huni U (by omega), hU]; norm_num)]
    have h45 : Nat.choose 10 2 = 45 := by decide
    rw [h45]
    norm_num
  -- the shadow inequality bounds `P p 5` from below, the local bounds from above
  have hsh := shadow_ineq p h0 hcompl hshadow h1 h2
  have h3 := P_three_ge p h0 hloc
  have h5 := P_five_le p h0 hcompl hloc hB
  have htot' : (((powersetCard 5 (univ : Finset (Fin 10))).filter
      (fun A => p A = 1 / 32)).card : ℝ) + (((powersetCard 5 (univ : Finset (Fin 10))).filter
      (fun A => ¬ p A = 1 / 32)).card : ℝ) = 252 := by
    exact_mod_cast htot
  have hB' : (((powersetCard 5 (univ : Finset (Fin 10))).filter
      (fun A => ¬ p A = 1 / 32)).card : ℝ) ≤ 43 := by
    exact_mod_cast hB
  linarith

end QuantumExtremalNumber.Abstract10
