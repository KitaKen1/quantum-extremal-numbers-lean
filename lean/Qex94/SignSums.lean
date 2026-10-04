import Mathlib

/-!
# Sign sums over sites

For a set `T` of sites let `ε_i = -1` for `i ∈ T` and `ε_i = 1` otherwise, so
`s = ∑ ε = n - 2|T|`. The shadow inequality with `+` sites `E` has the coefficient
`∏_{l ∈ T} (±1) = (-1)^|T| ∏_{i ∈ E} ε_i`. Summing over ordered pairs and triples of distinct
sites gives `∑_{i ≠ j} ε_i ε_j = s² - n` and `∑ ε_i ε_j ε_k = s³ - 3 n s + 2 s`.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.SignSums

variable {n : ℕ}

/-- The sign of a site: `-1` inside `T`, `1` outside. -/
def sgnIn (T : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ T then -1 else 1

lemma sgnIn_mul_self (T : Finset (Fin n)) (i : Fin n) : sgnIn T i * sgnIn T i = 1 := by
  unfold sgnIn
  split_ifs <;> norm_num

lemma sum_sgnIn (T : Finset (Fin n)) : ∑ i : Fin n, sgnIn T i = n - 2 * T.card := by
  rw [← Finset.sum_add_sum_compl T]
  rw [Finset.sum_congr rfl (fun i hi => show sgnIn T i = -1 by simp [sgnIn, hi]),
    Finset.sum_congr rfl (fun i hi => show sgnIn T i = 1 by
      simp [sgnIn, Finset.mem_compl.mp hi])]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_compl, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul]
  have hle : T.card ≤ n := by simpa using Finset.card_le_univ T
  rw [Nat.cast_sub hle]
  ring

lemma prod_sign_triple (T : Finset (Fin n)) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ∏ l ∈ T, (if l ∈ ({i, j, k} : Finset (Fin n)) then (1 : ℝ) else -1) =
      (-1) ^ T.card * (sgnIn T i * sgnIn T j * sgnIn T k) := by
  have hl : ∀ l : Fin n, (if l ∈ ({i, j, k} : Finset (Fin n)) then (1 : ℝ) else -1) =
      (-1) * ((if l = i then -1 else 1) * (if l = j then -1 else 1) *
        (if l = k then -1 else 1)) := by
    intro l
    by_cases hi : l = i
    · subst hi
      simp [hij, hik]
    · by_cases hj : l = j
      · subst hj
        simp [hi, hjk]
      · by_cases hk : l = k
        · subst hk
          simp [hi, hj]
        · simp [hi, hj, hk]
  rw [Finset.prod_congr rfl (fun l _ => hl l), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
    Finset.prod_ite_eq']
  rfl

/-- The sum over ordered triples of distinct sites:
`∑_{i} ∑_{j ≠ i} ∑_{k ∉ {i, j}} ε_i ε_j ε_k = s³ - 3 n s + 2 s` with `s = ∑ ε`, since `ε² = 1`. -/
lemma sum_triple_sgnIn (T : Finset (Fin n)) :
    ∑ i : Fin n, ∑ j ∈ univ.erase i, ∑ k ∈ (univ.erase i).erase j,
      sgnIn T i * sgnIn T j * sgnIn T k =
      ((n : ℝ) - 2 * T.card) ^ 3 - 3 * n * ((n : ℝ) - 2 * T.card) +
        2 * ((n : ℝ) - 2 * T.card) := by
  set e := sgnIn T with he
  set s : ℝ := ∑ i : Fin n, e i with hs
  have hs' : s = (n : ℝ) - 2 * T.card := sum_sgnIn T
  have hee : ∀ a, e a * e a = 1 := sgnIn_mul_self T
  have hinner : ∀ i j : Fin n, j ∈ univ.erase i →
      ∑ k ∈ (univ.erase i).erase j, e i * e j * e k = e i * e j * (s - e i - e j) := by
    intro i j hj
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj, Finset.sum_erase_eq_sub (mem_univ i)]
  have hmid : ∀ i : Fin n, ∑ j ∈ univ.erase i, e i * e j * (s - e i - e j) =
      e i * ((s - e i) * (s - e i) - (n - 1)) := by
    intro i
    have h1 : ∑ j ∈ univ.erase i, e i * e j * (s - e i - e j) =
        e i * ((s - e i) * ∑ j ∈ univ.erase i, e j - ∑ j ∈ univ.erase i, e j * e j) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, Finset.sum_erase_eq_sub (mem_univ i), Finset.sum_congr rfl fun j _ => hee j,
      Finset.sum_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact i.elim0
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => (Finset.sum_congr rfl fun j hj => hinner i j hj).trans
    (hmid i)]
  have hcube : ∑ i : Fin n, e i * ((s - e i) * (s - e i) - (n - 1)) =
      s * s * s - 3 * n * s + 2 * s := by
    have h1 : ∀ i, e i * ((s - e i) * (s - e i) - (n - 1)) =
        (s * s - (n - 1) + 1) * e i - 2 * s := fun i => by
      linear_combination (e i - 2 * s) * hee i
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hs,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcube, hs']
  ring

lemma prod_sign_empty (T : Finset (Fin n)) :
    ∏ l ∈ T, (if l ∈ (∅ : Finset (Fin n)) then (1 : ℝ) else -1) = (-1) ^ T.card := by
  simp

lemma prod_sign_pair (T : Finset (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    ∏ l ∈ T, (if l ∈ ({i, j} : Finset (Fin n)) then (1 : ℝ) else -1) =
      (-1) ^ T.card * (sgnIn T i * sgnIn T j) := by
  have hl : ∀ l : Fin n, (if l ∈ ({i, j} : Finset (Fin n)) then (1 : ℝ) else -1) =
      (-1) * ((if l = i then -1 else 1) * (if l = j then -1 else 1)) := by
    intro l
    by_cases hi : l = i
    · subst hi
      simp [hij]
    · by_cases hj : l = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  rw [Finset.prod_congr rfl (fun l _ => hl l), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  rfl

/-- `∑_{i ≠ j} ε_i ε_j = (∑ ε)² - ∑ ε²`. -/
lemma sum_pair_sgnIn (T : Finset (Fin n)) :
    ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else sgnIn T i * sgnIn T j) =
      ((n : ℝ) - 2 * T.card) ^ 2 - n := by
  have h : ∀ i j : Fin n, (if i = j then (0 : ℝ) else sgnIn T i * sgnIn T j) =
      sgnIn T i * sgnIn T j - (if i = j then sgnIn T i * sgnIn T j else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_mul_sum, sum_sgnIn, sgnIn_mul_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

lemma sum_three_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

end QuantumExtremalNumber.SignSums
