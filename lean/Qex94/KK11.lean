import Mathlib

/-!
# A Kruskal–Katona bound for six-sets of eleven points

Any fourteen six-element subsets of an eleven-element set have at least forty five-element
subsets in their shadow. This follows from Mathlib's Kruskal–Katona theorem: the first fourteen
six-sets in colex order form the initial segment below `{0, 1, 2, 3, 6, 7}`, and its shadow is
the initial segment below `{1, 2, 3, 6, 7}`, which has `21 + 15 + 4 = 40` elements.
-/

open scoped BigOperators
open Finset

namespace QuantumExtremalNumber.KK11

/-- The colex initial segment below `{0, 1, 2, 3, 6, 7}` consists of fourteen six-sets
(checked by kernel computation). -/
lemma card_initSeg_six : (Colex.initSeg ({0, 1, 2, 3, 6, 7} : Finset (Fin 11))).card = 14 := by
  decide +kernel

/-- The colex initial segment below `{0, 1, 2, 3, 6, 7}` is an initial segment of six-sets. -/
lemma isInitSeg_initSeg_six :
    Colex.IsInitSeg (Colex.initSeg ({0, 1, 2, 3, 6, 7} : Finset (Fin 11))) 6 :=
  Colex.isInitSeg_initSeg

/-- The shadow of the colex initial segment below `{0, 1, 2, 3, 6, 7}` is the colex initial
segment below `{1, 2, 3, 6, 7}`. -/
lemma shadow_initSeg_six :
    Finset.shadow (Colex.initSeg ({0, 1, 2, 3, 6, 7} : Finset (Fin 11))) =
      Colex.initSeg ({1, 2, 3, 6, 7} : Finset (Fin 11)) := by
  rw [Colex.shadow_initSeg (by decide)]
  exact congrArg Colex.initSeg (by decide)

/-- The colex initial segment below `{1, 2, 3, 6, 7}` consists of `21 + 15 + 4 = 40` five-sets
(checked by kernel computation). -/
lemma card_initSeg_five : (Colex.initSeg ({1, 2, 3, 6, 7} : Finset (Fin 11))).card = 40 := by
  decide +kernel

theorem forty_le_card_shadow (𝒜 : Finset (Finset (Fin 11))) (h𝒜 : ∀ A ∈ 𝒜, A.card = 6)
    (hcard : 14 ≤ 𝒜.card) : 40 ≤ (Finset.shadow 𝒜).card := by
  have hsized : (𝒜 : Set (Finset (Fin 11))).Sized 6 := fun A hA => h𝒜 A hA
  have h := kruskal_katona hsized (card_initSeg_six.trans_le hcard) isInitSeg_initSeg_six
  rwa [shadow_initSeg_six, card_initSeg_five] at h

end QuantumExtremalNumber.KK11
