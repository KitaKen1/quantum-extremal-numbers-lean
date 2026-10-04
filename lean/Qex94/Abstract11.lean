import Qex94.PurityFacts

/-!
# The combinatorial core for eleven qubits

A real function `p` on subsets of eleven qubits with the purity axioms, the shadow inequality
`S_3 ≥ 0`, the subsystem shadow inequalities and the nonnegativity of the Möbius coefficients
allows at most `422` five-sets with minimal purity `1/32`. The Kruskal–Katona bound needed
here is a hypothesis, discharged in `Qex94/KK11.lean`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.Abstract11

open PurityFacts

/-! ### Sums over subsets -/

/-- Grouping a sum over the subsets of `S` by cardinality. -/
lemma sum_powerset_card_mul {α : Type*} (S : Finset α) (c : ℕ → ℝ) (g : Finset α → ℝ) :
    ∑ U ∈ S.powerset, c U.card * g U =
      ∑ k ∈ range (S.card + 1), c k * ∑ U ∈ powersetCard k S, g U := by
  rw [← sum_fiberwise_of_maps_to (s := S.powerset) (t := range (S.card + 1)) (g := card)
    (fun U hU => by rw [mem_range, Nat.lt_succ_iff]; exact card_le_card (mem_powerset.1 hU))]
  refine sum_congr rfl fun k _ => ?_
  rw [powersetCard_eq_filter, mul_sum]
  exact sum_congr rfl fun U hU => by rw [(mem_filter.1 hU).2]

/-- Removing one point is a bijection from `R` onto its subsets of size `#R - 1`. -/
lemma sum_powersetCard_eq_sum_erase {α : Type*} [DecidableEq α] (R : Finset α) (k : ℕ)
    (hR : R.card = k + 1) (f : Finset α → ℝ) :
    ∑ T ∈ powersetCard k R, f T = ∑ i ∈ R, f (R.erase i) := by
  symm
  apply sum_nbij (fun i => R.erase i)
  · intro i hi
    rw [mem_powersetCard, card_erase_of_mem hi, hR]
    exact ⟨erase_subset i R, rfl⟩
  · exact erase_injOn R
  · intro T hT
    rw [mem_coe, mem_powersetCard] at hT
    obtain ⟨i, hi, hiT⟩ := exists_eq_insert_iff.2 ⟨hT.1, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · rw [mem_coe, ← hiT]
      exact mem_insert_self i T
    · show R.erase i = T
      rw [← hiT, erase_insert hi]
  · intro i _
    rfl

/-- Double counting: every `k`-subset of `S` is `R.erase i` for `#S - k` pairs `(R, i)`. -/
lemma sum_sum_erase {α : Type*} [DecidableEq α] (S : Finset α) (m k : ℕ) (hm : m = k + 1)
    (f : Finset α → ℝ) :
    ∑ R ∈ powersetCard m S, ∑ i ∈ R, f (R.erase i) =
      ((S.card - k : ℕ) : ℝ) * ∑ T ∈ powersetCard k S, f T := by
  subst hm
  rw [sum_sigma']
  have : ∑ x ∈ (powersetCard (k + 1) S).sigma (fun R => R), f (x.1.erase x.2) =
      ∑ y ∈ (powersetCard k S).sigma (fun T => S \ T), f y.1 := by
    apply sum_nbij' (fun x => ⟨x.1.erase x.2, x.2⟩) (fun y => ⟨insert y.2 y.1, y.2⟩)
    · simp only [mem_sigma, mem_powersetCard, mem_sdiff]
      rintro ⟨R, i⟩ ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨(erase_subset i R).trans h1, by rw [card_erase_of_mem h3, h2]; rfl⟩,
        h1 h3, notMem_erase i R⟩
    · simp only [mem_sigma, mem_powersetCard, mem_sdiff]
      rintro ⟨T, j⟩ ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨insert_subset h3 h1, by rw [card_insert_of_notMem h4, h2]⟩, mem_insert_self _ _⟩
    · simp only [mem_sigma]
      rintro ⟨R, i⟩ ⟨_, h2⟩
      simp [insert_erase h2]
    · simp only [mem_sigma, mem_sdiff]
      rintro ⟨T, j⟩ ⟨_, _, h4⟩
      simp [erase_insert h4]
    · intro x _
      rfl
  rw [this, ← sum_sigma' (powersetCard k S) (fun T => S \ T) (fun T _ => f T), mul_sum]
  refine sum_congr rfl fun T hT => ?_
  rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset (mem_powersetCard.1 hT).1,
    (mem_powersetCard.1 hT).2]

/-! ### Bad five-sets and two-uniformity -/

/-- The five-sets whose purity is not minimal. -/
noncomputable def bad (p : Finset (Fin 11) → ℝ) : Finset (Finset (Fin 11)) :=
  (powersetCard 5 univ).filter (fun A => ¬ p A = 1 / 32)

/-- Membership in `bad p`. -/
lemma mem_bad {p : Finset (Fin 11) → ℝ} {S : Finset (Fin 11)} :
    S ∈ bad p ↔ S.card = 5 ∧ ¬ p S = 1 / 32 := by
  rw [bad, mem_filter, mem_powersetCard, and_iff_right (subset_univ S)]

/-- At most 39 bad five-sets force `p U = (1/2)^|U|` for every `U` with `|U| ≤ 2`. -/
lemma uniform_of_few_bad (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : (bad p).card ≤ 39) (U : Finset (Fin 11)) (hU : U.card ≤ 2) :
    p U = (1 / 2 : ℝ) ^ U.card := by
  have hex : ∃ S ∈ powersetCard 5 (univ : Finset (Fin 11)), U ⊆ S ∧ p S = 1 / 32 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hsub : (powersetCard 5 (univ : Finset (Fin 11))).filter (fun S => U ⊆ S) ⊆ bad p := by
      intro S hS
      rw [mem_filter] at hS
      rw [bad, mem_filter]
      exact ⟨hS.1, hne S hS.1 hS.2⟩
    have h1 := card_le_card hsub
    have h2 := choose_le_card_supersets 5 U (by omega)
    have h3 : 40 ≤ Nat.choose (11 - U.card) (5 - U.card) := by
      obtain h | h | h : U.card = 0 ∨ U.card = 1 ∨ U.card = 2 := by omega
      all_goals rw [h]; decide
    omega
  obtain ⟨S, hS, hUS, hpS⟩ := hex
  apply eq_half_pow_of_subset p h0 hloc U S hUS
  rw [hpS, (mem_powersetCard.1 hS).2]
  norm_num

/-- The level sums of a two-uniform `p` inside a set `S`. -/
lemma sum_powersetCard_of_uniform (p : Finset (Fin 11) → ℝ)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card)
    (S : Finset (Fin 11)) (k : ℕ) (hk : k ≤ 2) :
    ∑ U ∈ powersetCard k S, p U = (S.card.choose k : ℝ) * (1 / 2) ^ k := by
  have h : ∀ U ∈ powersetCard k S, p U = (1 / 2 : ℝ) ^ k := by
    intro U hU
    rw [mem_powersetCard] at hU
    rw [huni U (by omega), hU.2]
  rw [sum_congr rfl h, sum_const, card_powersetCard, nsmul_eq_mul]

/-! ### Level sums and the shadow inequality -/

/-- The level sum of the empty set. -/
lemma P_zero (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1) : P p 0 = 1 := by
  unfold P
  rw [powersetCard_zero, sum_singleton, h0]

/-- The first level sum of a two-uniform `p`. -/
lemma P_one (p : Finset (Fin 11) → ℝ)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card) :
    P p 1 = 11 / 2 := by
  unfold P
  rw [sum_powersetCard_of_uniform p huni univ 1 (by norm_num), card_univ, Fintype.card_fin]
  norm_num

/-- The second level sum of a two-uniform `p`. -/
lemma P_two (p : Finset (Fin 11) → ℝ)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card) :
    P p 2 = 55 / 4 := by
  unfold P
  rw [sum_powersetCard_of_uniform p huni univ 2 (by norm_num), card_univ, Fintype.card_fin,
    show Nat.choose 11 2 = 55 by decide]
  norm_num

/-- The lower bound `165/8 ≤ P p 3`. -/
lemma P_three_ge (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W)) :
    165 / 8 ≤ P p 3 := by
  have h : ∀ T ∈ powersetCard 3 (univ : Finset (Fin 11)), (1 / 8 : ℝ) ≤ p T := by
    intro T hT
    have := half_pow_le p h0 hloc T
    rw [(mem_powersetCard.1 hT).2] at this
    norm_num at this
    exact this
  have hsum := sum_le_sum h
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    show Nat.choose 11 3 = 165 by decide, nsmul_eq_mul] at hsum
  unfold P
  norm_num at hsum
  linarith

/-- The shadow inequality `S_3 ≥ 0`, once the first three level sums are known. -/
lemma shadow_ineq (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hshadow3 : 0 ≤ ∑ T : Finset (Fin 11), (-1 : ℝ) ^ T.card *
      ((11 - 2 * (T.card : ℝ)) ^ 3 - 31 * (11 - 2 * (T.card : ℝ))) * p T)
    (h1 : P p 1 = 11 / 2) (h2 : P p 2 = 55 / 4) :
    0 ≤ 165 + 20 * P p 3 - 44 * P p 4 + 20 * P p 5 := by
  rw [sum_eq_sum_P p (fun k => (-1 : ℝ) ^ k *
    ((11 - 2 * (k : ℝ)) ^ 3 - 31 * (11 - 2 * (k : ℝ))))] at hshadow3
  simp only [sum_range_succ, sum_range_zero] at hshadow3
  norm_num at hshadow3
  have e0 := P_zero p h0
  have c11 := P_compl p hcompl 0 11 rfl
  have c10 := P_compl p hcompl 1 10 rfl
  have c9 := P_compl p hcompl 2 9 rfl
  have c8 := P_compl p hcompl 3 8 rfl
  have c7 := P_compl p hcompl 4 7 rfl
  have c6 := P_compl p hcompl 5 6 rfl
  linarith

/-! ### The Möbius coefficients of four-sets -/

/-- The Möbius coefficient of a four-set, for a two-uniform `p`. -/
noncomputable def a (p : Finset (Fin 11) → ℝ) (R : Finset (Fin 11)) : ℝ :=
  16 * p R - 8 * ∑ T ∈ powersetCard 3 R, p T + 3

/-- For a four-set `R`, the Möbius inequality says `0 ≤ a p R`. -/
lemma a_nonneg (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card)
    (hmob : ∀ R : Finset (Fin 11),
      0 ≤ ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * 2 ^ U.card * p U)
    (R : Finset (Fin 11)) (hR : R.card = 4) : 0 ≤ a p R := by
  have h := hmob R
  rw [sum_powerset_card_mul R (fun k => (-1 : ℝ) ^ (R.card - k) * 2 ^ k) p] at h
  have e4 : powersetCard 4 R = {R} := by rw [← hR, powersetCard_self]
  rw [hR] at h
  simp only [sum_range_succ, sum_range_zero, powersetCard_zero, sum_singleton, e4] at h
  rw [sum_powersetCard_of_uniform p huni R 1 (by norm_num),
    sum_powersetCard_of_uniform p huni R 2 (by norm_num), hR, h0,
    show Nat.choose 4 2 = 6 by decide] at h
  unfold a
  norm_num at h
  linarith

/-- The sum of `a` over all four-sets, in terms of level sums. -/
lemma sum_a_eq (p : Finset (Fin 11) → ℝ) :
    ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), a p R = 16 * P p 4 - 64 * P p 3 + 990 := by
  have hdc : ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), ∑ T ∈ powersetCard 3 R, p T =
      8 * P p 3 := by
    rw [sum_congr rfl fun R hR => sum_powersetCard_eq_sum_erase R 3
      (mem_powersetCard.1 hR).2 p, sum_sum_erase univ 4 3 rfl p, card_univ, Fintype.card_fin]
    rfl
  unfold a
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hdc, sum_const, card_powersetCard,
    card_univ, Fintype.card_fin, show Nat.choose 11 4 = 330 by decide, nsmul_eq_mul]
  unfold P
  norm_num
  ring

/-- The sum of `a` over the four-subsets of a five-set `S` is at most the total sum. -/
lemma sum_a_subset_le (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card)
    (hmob : ∀ R : Finset (Fin 11),
      0 ≤ ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * 2 ^ U.card * p U)
    (S : Finset (Fin 11)) :
    ∑ R ∈ powersetCard 4 S, a p R ≤ ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), a p R :=
  sum_le_sum_of_subset_of_nonneg (powersetCard_mono (subset_univ S))
    (fun R hR _ => a_nonneg p h0 huni hmob R (mem_powersetCard.1 hR).2)

/-- The subsystem inequality for a five-set `S`, in terms of `a`. -/
lemma le_of_sub (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card)
    (hsub : ∀ S : Finset (Fin 11), 0 ≤ ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * p T)
    (S : Finset (Fin 11)) (hS : S.card = 5) :
    32 * p S - 1 ≤ 1 + 2 * ∑ R ∈ powersetCard 4 S, a p R := by
  have h := hsub S
  rw [sum_powerset_card_mul S (fun k => (-1 : ℝ) ^ k) p] at h
  have e5 : powersetCard 5 S = {S} := by rw [← hS, powersetCard_self]
  rw [hS] at h
  simp only [sum_range_succ, sum_range_zero, powersetCard_zero, sum_singleton, e5] at h
  rw [sum_powersetCard_of_uniform p huni S 1 (by norm_num),
    sum_powersetCard_of_uniform p huni S 2 (by norm_num), hS, h0,
    show Nat.choose 5 2 = 10 by decide] at h
  have hdc : ∑ R ∈ powersetCard 4 S, ∑ T ∈ powersetCard 3 R, p T =
      2 * ∑ T ∈ powersetCard 3 S, p T := by
    rw [sum_congr rfl fun R hR => sum_powersetCard_eq_sum_erase R 3
      (mem_powersetCard.1 hR).2 p, sum_sum_erase S 4 3 rfl p, hS]
    norm_num
  have ht : ∑ R ∈ powersetCard 4 S, a p R =
      16 * ∑ R ∈ powersetCard 4 S, p R - 16 * ∑ T ∈ powersetCard 3 S, p T + 15 := by
    unfold a
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hdc, sum_const,
      card_powersetCard, hS]
    norm_num
    ring
  rw [ht]
  norm_num at h
  linarith

/-! ### Local upper bounds for five-sets -/

/-- A good five-set disjoint from the five-set `S` forces `p S ≤ 1/16`. -/
lemma le_of_disjoint_good (p : Finset (Fin 11) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S R : Finset (Fin 11)) (hS : S.card = 5) (hR : R.card = 5) (hRS : Disjoint R S)
    (hp : p R = 1 / 32) : p S ≤ 1 / 16 := by
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

/-- A four-subset of minimal purity forces `p S ≤ 1/8`. -/
lemma le_of_good_erase (p : Finset (Fin 11) → ℝ) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S : Finset (Fin 11)) (i : Fin 11) (hi : i ∈ S) (hp : p (S.erase i) = 1 / 16) :
    p S ≤ 1 / 8 := by
  have := up_le p hcompl hloc i (S.erase i) (notMem_erase i S)
  rw [insert_erase hi, hp] at this
  linarith

/-! ### Few five-sets with only bad five-sets disjoint from them -/

/-- At most 13 bad five-sets have only bad five-sets disjoint from them. -/
lemma card_H_le (B : Finset (Finset (Fin 11))) (hB : B ⊆ powersetCard 5 univ)
    (hBc : B.card ≤ 39)
    (hKK : ∀ 𝒜 : Finset (Finset (Fin 11)), (∀ A ∈ 𝒜, A.card = 6) → 14 ≤ 𝒜.card →
      40 ≤ (Finset.shadow 𝒜).card) :
    (B.filter (fun S =>
      ∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ B)).card ≤ 13 := by
  set H := B.filter (fun S =>
      ∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ B) with hH
  have h5 : ∀ S ∈ H, S.card = 5 := fun S hS =>
    (mem_powersetCard.1 (hB (mem_filter.1 hS).1)).2
  have h6 : ∀ A ∈ H.image compl, A.card = 6 := by
    intro A hA
    rw [mem_image] at hA
    obtain ⟨S, hS, rfl⟩ := hA
    rw [card_compl, Fintype.card_fin, h5 S hS]
  have hc : (H.image compl).card = H.card := card_image_of_injective H compl_injective
  have hsh : Finset.shadow (H.image compl) ⊆ B := by
    intro T hT
    rw [mem_shadow_iff] at hT
    obtain ⟨A, hA, x, hx, rfl⟩ := hT
    rw [mem_image] at hA
    obtain ⟨S, hS, rfl⟩ := hA
    have hS5 := h5 S hS
    rw [hH, mem_filter] at hS
    apply hS.2
    · rw [mem_powersetCard, card_erase_of_mem hx, card_compl, Fintype.card_fin, hS5]
      exact ⟨subset_univ _, rfl⟩
    · exact disjoint_of_subset_left (erase_subset x Sᶜ) disjoint_compl_left
  by_contra hcon
  have := hKK _ h6 (by omega)
  have := card_le_card hsh
  omega

/-! ### Few five-sets without a four-subset of minimal purity -/

/-- The thirty five-sets meeting the five-set `S` in four points. -/
def F (S : Finset (Fin 11)) : Finset (Finset (Fin 11)) :=
  (S ×ˢ Sᶜ).image (fun q : Fin 11 × Fin 11 => insert q.2 (S.erase q.1))

/-- `F S` has thirty elements. -/
lemma card_F (S : Finset (Fin 11)) (hS : S.card = 5) : (F S).card = 30 := by
  rw [F, card_image_of_injOn, card_product, card_compl, Fintype.card_fin, hS]
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

/-- Two different five-sets have at most eleven such five-sets in common. -/
lemma card_F_inter_le (S S' : Finset (Fin 11)) (hS : S.card = 5) (hS' : S'.card = 5)
    (hne : S ≠ S') : (F S ∩ F S').card ≤ 11 := by
  obtain ⟨a, haS, haS'⟩ : ∃ a ∈ S, a ∉ S' := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (eq_of_subset_of_card_le h (by omega))
  have hsub : F S ∩ F S' ⊆ Sᶜ.image (fun x => insert x (S.erase a)) ∪
      S'.image (fun j => insert a (S'.erase j)) := by
    intro T hT
    rw [mem_inter] at hT
    simp only [F, mem_image, mem_product, mem_compl, Prod.exists] at hT
    obtain ⟨⟨i, x, ⟨hi, hx⟩, hT1⟩, ⟨j, y, ⟨hj, hy⟩, hT2⟩⟩ := hT
    rw [mem_union, mem_image, mem_image]
    by_cases haT : a ∈ T
    · right
      refine ⟨j, hj, ?_⟩
      rw [← hT2] at haT
      rcases mem_insert.1 haT with h | h
      · rw [h, hT2]
      · exact absurd (mem_of_mem_erase h) haS'
    · left
      refine ⟨x, mem_compl.2 hx, ?_⟩
      have hai : a = i := by
        by_contra hai
        exact haT (hT1 ▸ mem_insert_of_mem (mem_erase.2 ⟨hai, haS⟩))
      rw [hai, hT1]
  calc (F S ∩ F S').card
      ≤ (Sᶜ.image (fun x => insert x (S.erase a)) ∪
          S'.image (fun j => insert a (S'.erase j))).card := card_le_card hsub
    _ ≤ (Sᶜ.image (fun x => insert x (S.erase a))).card +
          (S'.image (fun j => insert a (S'.erase j))).card := card_union_le _ _
    _ ≤ Sᶜ.card + S'.card := add_le_add card_image_le card_image_le
    _ = 11 := by rw [card_compl, Fintype.card_fin, hS, hS']

/-- If no four-subset of `S` has minimal purity, all thirty five-sets in `F S` are bad. -/
lemma F_subset_bad (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (S : Finset (Fin 11)) (hS : S.card = 5) (hX : ∀ i ∈ S, ¬ p (S.erase i) = 1 / 16) :
    F S ⊆ bad p := by
  intro T hT
  simp only [F, mem_image, mem_product, mem_compl, Prod.exists] at hT
  obtain ⟨i, x, ⟨hi, hx⟩, rfl⟩ := hT
  have hx' : x ∉ S.erase i := fun h => hx (mem_of_mem_erase h)
  have hcard : (insert x (S.erase i)).card = 5 := by
    rw [card_insert_of_notMem hx', card_erase_of_mem hi, hS]
  refine mem_bad.2 ⟨hcard, fun hpT => hX i hi ?_⟩
  have := eq_half_pow_of_subset p h0 hloc (S.erase i) (insert x (S.erase i))
    (subset_insert _ _) (by rw [hpT, hcard]; norm_num)
  rw [this, card_erase_of_mem hi, hS]
  norm_num

/-- At most one bad five-set has no four-subset of minimal purity. -/
lemma card_X_le_one (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hB : (bad p).card ≤ 39) :
    ((bad p).filter (fun S => ∀ i ∈ S, ¬ p (S.erase i) = 1 / 16)).card ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨S, hS, S', hS', hne⟩ := one_lt_card.1 hcon
  rw [mem_filter] at hS hS'
  have h5 := (mem_bad.1 hS.1).1
  have h5' := (mem_bad.1 hS'.1).1
  have h1 := F_subset_bad p h0 hloc S h5 hS.2
  have h2 := F_subset_bad p h0 hloc S' h5' hS'.2
  have h3 := card_le_card (union_subset h1 h2)
  have h4 := card_union_add_card_inter (F S) (F S')
  have h6 := card_F_inter_le S S' h5 h5' hne
  rw [card_F S h5, card_F S' h5'] at h4
  omega

/-! ### Assembling the argument -/

/-- The excess of `P p 5` over its minimum comes from the bad five-sets. -/
lemma P_five_eq (p : Finset (Fin 11) → ℝ) :
    32 * P p 5 - 462 = ∑ S ∈ bad p, (32 * p S - 1) := by
  have htot := card_filter_add_card_filter_not (s := powersetCard 5 (univ : Finset (Fin 11)))
    (fun A => p A = 1 / 32)
  rw [card_powersetCard, card_univ, Fintype.card_fin, show Nat.choose 11 5 = 462 by decide]
    at htot
  have htot' : (((powersetCard 5 (univ : Finset (Fin 11))).filter
      (fun A => p A = 1 / 32)).card : ℝ) + ((bad p).card : ℝ) = 462 := by
    exact_mod_cast htot
  have hG : ∑ S ∈ (powersetCard 5 (univ : Finset (Fin 11))).filter (fun A => p A = 1 / 32),
      p S = (((powersetCard 5 (univ : Finset (Fin 11))).filter
        (fun A => p A = 1 / 32)).card : ℝ) * (1 / 32) := by
    rw [sum_congr rfl (fun S hS => (mem_filter.1 hS).2), sum_const, nsmul_eq_mul]
  have hP : P p 5 = ∑ S ∈ (powersetCard 5 (univ : Finset (Fin 11))).filter
      (fun A => p A = 1 / 32), p S + ∑ S ∈ bad p, p S :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hP, hG]
  linarith

/-- The per-set bound for bad five-sets. -/
lemma bound_bad (p : Finset (Fin 11) → ℝ) (h0 : p ∅ = 1) (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hsub : ∀ S : Finset (Fin 11), 0 ≤ ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * p T)
    (hmob : ∀ R : Finset (Fin 11),
      0 ≤ ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * 2 ^ U.card * p U)
    (huni : ∀ U : Finset (Fin 11), U.card ≤ 2 → p U = (1 / 2 : ℝ) ^ U.card)
    (S : Finset (Fin 11)) (hS : S ∈ bad p) :
    32 * p S - 1 ≤ 1 +
      (if ∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ bad p
        then (2 : ℝ) else 0) +
      (if ∀ i ∈ S, ¬ p (S.erase i) = 1 / 16
        then 2 * ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), a p R else 0) := by
  have hS5 := (mem_bad.1 hS).1
  have ht0 : 0 ≤ ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), a p R :=
    sum_nonneg fun R hR => a_nonneg p h0 huni hmob R (mem_powersetCard.1 hR).2
  have hnotH : ¬ (∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ bad p) →
      32 * p S - 1 ≤ 1 := by
    intro hH
    simp only [not_forall] at hH
    obtain ⟨R, hR, hRS, hRB⟩ := hH
    have hpR : p R = 1 / 32 := by
      by_contra hpR
      exact hRB (mem_bad.2 ⟨(mem_powersetCard.1 hR).2, hpR⟩)
    have := le_of_disjoint_good p hcompl hloc S R hS5 (mem_powersetCard.1 hR).2 hRS hpR
    linarith
  split_ifs with hH hX hX
  · have h1 := le_of_sub p h0 huni hsub S hS5
    have h2 := sum_a_subset_le p h0 huni hmob S
    linarith
  · simp only [not_forall, not_not] at hX
    obtain ⟨i, hi, hpi⟩ := hX
    have := le_of_good_erase p hcompl hloc S i hi hpi
    linarith
  · have := hnotH hH
    linarith
  · have := hnotH hH
    linarith

theorem abstract_bound_eleven (p : Finset (Fin 11) → ℝ)
    (h0 : p ∅ = 1)
    (hcompl : ∀ T, p Tᶜ = p T)
    (hloc : ∀ (i : Fin 11) (W : Finset (Fin 11)), i ∉ W → p W ≤ 2 * p (insert i W))
    (hshadow3 : 0 ≤ ∑ T : Finset (Fin 11), (-1 : ℝ) ^ T.card *
      ((11 - 2 * (T.card : ℝ)) ^ 3 - 31 * (11 - 2 * (T.card : ℝ))) * p T)
    (hsub : ∀ S : Finset (Fin 11), 0 ≤ ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * p T)
    (hmob : ∀ R : Finset (Fin 11),
      0 ≤ ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * 2 ^ U.card * p U)
    (hKK : ∀ 𝒜 : Finset (Finset (Fin 11)), (∀ A ∈ 𝒜, A.card = 6) → 14 ≤ 𝒜.card →
      40 ≤ (Finset.shadow 𝒜).card) :
    ((powersetCard 5 (univ : Finset (Fin 11))).filter (fun A => p A = 1 / 32)).card ≤ 422 := by
  by_contra hcon
  rw [not_le] at hcon
  -- at most `462 - 423 = 39` five-sets are bad
  have htot := card_filter_add_card_filter_not (s := powersetCard 5 (univ : Finset (Fin 11)))
    (fun A => p A = 1 / 32)
  rw [card_powersetCard, card_univ, Fintype.card_fin, show Nat.choose 11 5 = 462 by decide]
    at htot
  have hB : (bad p).card ≤ 39 := by
    change _ + (bad p).card = 462 at htot
    omega
  -- hence `p` is two-uniform, which pins down the first level sums
  have huni := uniform_of_few_bad p h0 hloc hB
  have hsh := shadow_ineq p h0 hcompl hshadow3 (P_one p huni) (P_two p huni)
  have hP3 := P_three_ge p h0 hloc
  -- the Möbius coefficients of four-sets
  have htP := sum_a_eq p
  set t := ∑ R ∈ powersetCard 4 (univ : Finset (Fin 11)), a p R
  have ht0 : 0 ≤ t := sum_nonneg fun R hR => a_nonneg p h0 huni hmob R (mem_powersetCard.1 hR).2
  -- the bad five-sets
  set H := (bad p).filter
    (fun S => ∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ bad p)
  set X := (bad p).filter (fun S => ∀ i ∈ S, ¬ p (S.erase i) = 1 / 16)
  have hHc : H.card ≤ 13 := card_H_le (bad p) (filter_subset _ _) hB hKK
  have hXc : X.card ≤ 1 := card_X_le_one p h0 hloc hB
  have hD : 32 * P p 5 - 462 ≤ (bad p).card + 2 * H.card + 2 * t * X.card := by
    rw [P_five_eq]
    calc ∑ S ∈ bad p, (32 * p S - 1)
        ≤ ∑ S ∈ bad p, (1 +
          (if ∀ R ∈ powersetCard 5 (univ : Finset (Fin 11)), Disjoint R S → R ∈ bad p
            then (2 : ℝ) else 0) +
          (if ∀ i ∈ S, ¬ p (S.erase i) = 1 / 16 then 2 * t else 0)) :=
          sum_le_sum fun S hS => bound_bad p h0 hcompl hloc hsub hmob huni S hS
      _ = (bad p).card + 2 * H.card + 2 * t * X.card := by
          rw [sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const,
            sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
          ring
  have hB' : ((bad p).card : ℝ) ≤ 39 := by exact_mod_cast hB
  have hH' : (H.card : ℝ) ≤ 13 := by exact_mod_cast hHc
  have hX' : (X.card : ℝ) ≤ 1 := by exact_mod_cast hXc
  have htX : t * X.card ≤ t := mul_le_of_le_one_right ht0 hX'
  linarith

end QuantumExtremalNumber.Abstract11
