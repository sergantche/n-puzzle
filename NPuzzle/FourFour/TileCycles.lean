import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.BlankReach

namespace NPuzzle.FourFour

/-!
Step **9b**: tile rearrangement with the blank (after 9a blank repositioning).

Classical plan: move blank to `bottomRight`, then apply local tile cycles / transpositions
until `tileList` matches `goal`, then recover `cfg = goal`.
-/

/-- Blank can be slid to the goal blank cell. -/
lemma reachable_blank_bottomRight (cfg : Config) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = bottomRight :=
  reachable_blank_any cfg bottomRight

/-- With blank at bottom-right, `parityClass` is `(invStat + 1) % 2`. -/
lemma parityClass_blank_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight) :
    parityClass cfg = (invStat cfg + 1) % 2 := by
  unfold parityClass
  rw [hbr, blankRow_bottomRight]

/-- With blank at bottom-right, `parityClass cfg = 1` means `invStat cfg` is even. -/
lemma invStat_even_of_parity_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (hpar : parityClass cfg = 1) : invStat cfg % 2 = 0 := by
  rw [parityClass_blank_bottomRight cfg hbr] at hpar
  omega

private lemma getElem_list_eq {α} {xs ys : List α} (h : xs = ys) {i : Nat} (hi : i < xs.length) :
    xs[i]'hi = ys[i]'(h ▸ hi) := by subst h; rfl

private lemma getElem_same_list {α} {xs : List α} {i j : Nat} (hij : i = j)
    (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

/-- Equal `tileList` and equal blank position determine all cell labels. -/
lemma cells_eq_of_tileList {cfg cfg' : Config}
    (hb : blank cfg = blank cfg') (ht : tileList cfg = tileList cfg') :
    ∀ c, cfg.cells c = cfg'.cells c := by
  intro c
  by_cases hc : c = blank cfg
  · subst hc
    rw [blank_zero cfg, hb, blank_zero cfg']
  · have hi := tileList_get_rankExcept cfg c hc
    have hj := tileList_get_rankExcept cfg' c (hb ▸ hc)
    have hrank : rankExcept (blank cfg) c = rankExcept (blank cfg') c := by simp [hb]
    have hidx : rankExcept (blank cfg) c < (tileList cfg).length := by
      unfold tileList; rw [List.length_map]; exact rankExcept_lt hc
    have hidx' : rankExcept (blank cfg) c < (tileList cfg').length := by rwa [← ht]
    have hlink :=
      getElem_same_list hrank hidx' (by
        unfold tileList; rw [List.length_map]; exact rankExcept_lt (hb ▸ hc))
    exact hi.symm.trans ((getElem_list_eq ht hidx).trans (hlink.trans hj))

/-- Matching `tileList` and blank cell implies configuration equality. -/
lemma config_eq_of_tileList_and_blank (cfg cfg' : Config)
    (hb : blank cfg = blank cfg') (ht : tileList cfg = tileList cfg') : cfg = cfg' :=
  Config.ext (cells_eq_of_tileList hb ht)

/-- Once `tileList` matches `goal` and blank stays at `bottomRight`, the board is solved. -/
lemma reachable_goal_of_tileList (cfg : Config) (hbr : blank cfg = bottomRight)
    (ht : tileList cfg = tileList goal) : Reachable cfg goal := by
  have heq : cfg = goal := by
    apply config_eq_of_tileList_and_blank cfg goal
    · rw [hbr, blank_goal]
    · exact ht
  rw [heq]
  exact Relation.ReflTransGen.refl

/-!
**Core combinatorial block (open, 9b.3):** from any `cfg` with `blank cfg = bottomRight` and
`parityClass cfg = 1`, legal moves rearrange tiles until `tileList cfg = tileList goal`.

Proof plan (classical):
1. Generator moves with blank on the bottom row (3-cycles on `{10,11,14,15}`, etc.).
2. Those generators realize all even permutations of `tileList` while `invStat` stays even
   (`invStat_even_of_parity_bottomRight`).
3. `invStat goal = 0`; reduce `invStat cfg` to `0`, then `reachable_goal_of_tileList`.
-/
lemma tiles_to_goal_at_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (hpar : parityClass cfg = 1) : Reachable cfg goal := by
  sorry

/-- Step 9c: assemble 9a (blank reposition) + 9b (tile rearrangement at bottom-right). -/
lemma parity_imp_reachable (cfg : Config) (h : parityClass cfg = 1) : Reachable cfg goal := by
  obtain ⟨cfg', hreach, hbr⟩ := reachable_blank_bottomRight cfg
  have hpar' : parityClass cfg' = 1 :=
    (parityClass_reachable hreach).symm.trans h
  exact Relation.ReflTransGen.trans hreach (tiles_to_goal_at_bottomRight cfg' hbr hpar')

end NPuzzle.FourFour
