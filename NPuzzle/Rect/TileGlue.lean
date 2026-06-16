import NPuzzle.Rect.Invariant

namespace NPuzzle.Rect

/-!
Rectangular glue between configurations and row-major tile lists.

This is the board-generic analogue of the first part of
`NPuzzle.FourFour.TileGlue`: a fixed blank cell plus the `tileList` determines
the entire configuration.
-/

private lemma getElem_list_eq {α} {xs ys : List α} (h : xs = ys)
    {i : Nat} (hi : i < xs.length) :
    xs[i]'hi = ys[i]'(h ▸ hi) := by
  subst h
  rfl

private lemma getElem_same_list {α} {xs : List α} {i j : Nat} (hij : i = j)
    (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by
  subst hij
  rfl

/-- Equal `tileList` and equal blank position determine all cell labels. -/
lemma cells_eq_of_tileList {B : Board} {cfg cfg' : Config B}
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
      rw [tileList_length]
      simpa [cellsRowMajorExcept_length] using rankExcept_lt hc
    have hidx' : rankExcept (blank cfg) c < (tileList cfg').length := by
      rw [← ht]
      exact hidx
    have hlink :=
      getElem_same_list hrank hidx' (by
        rw [tileList_length]
        simpa [cellsRowMajorExcept_length] using rankExcept_lt (hb ▸ hc))
    exact hi.symm.trans ((getElem_list_eq ht hidx).trans (hlink.trans hj))

/-- Matching `tileList` and blank cell implies configuration equality. -/
lemma config_eq_of_tileList_and_blank {B : Board} (cfg cfg' : Config B)
    (hb : blank cfg = blank cfg') (ht : tileList cfg = tileList cfg') : cfg = cfg' :=
  Config.ext (cells_eq_of_tileList hb ht)

/-- Once `tileList` matches `goal` and blank stays at `bottomRight`, the board is solved. -/
lemma reachable_goal_of_tileList {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B)
    (ht : tileList cfg = tileList (goal B)) : Reachable cfg (goal B) := by
  have heq : cfg = goal B := by
    apply config_eq_of_tileList_and_blank cfg (goal B)
    · rw [hbr, blank_goal]
    · exact ht
  rw [heq]
  exact Relation.ReflTransGen.refl

/-- Labels in `tileList` lie in `1…B.tileCount`. -/
lemma tileList_mem_Icc {B : Board} (cfg : Config B) {x : ℕ}
    (hx : x ∈ tileList cfg) :
    1 ≤ x ∧ x ≤ B.tileCount := by
  rw [tileList] at hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have hne := cellsRowMajorExcept_ne hc
  have hpos : cfg.cells c ≠ 0 := by
    intro h0
    have : c = blank cfg :=
      (ExistsUnique.unique cfg.valid.2.1 (blank_zero cfg) h0).symm
    exact hne this
  exact ⟨by omega, cfg.valid.1 c⟩

/-- Goal tile list is the canonical row-major list `1, …, B.tileCount`. -/
lemma tileList_goal (B : Board) :
    tileList (goal B) = (List.range B.tileCount).map (· + 1) := by
  rw [tileList, blank_goal]
  apply List.ext_getElem
  · rw [List.length_map, cellsRowMajorExcept_length, List.length_map, List.length_range]
  · intro i hi hi'
    rw [List.getElem_map, List.getElem_map]
    have hicells : i < (cellsRowMajorExcept (bottomRight B)).length := by
      simpa [List.length_map] using hi
    let c := (cellsRowMajorExcept (bottomRight B))[i]'hicells
    have hc : c ≠ bottomRight B := cellsRowMajorExcept_ne (List.getElem_mem hicells)
    have hrank : rankExcept (bottomRight B) c = i :=
      rankExcept_cellsRowMajorExcept (bottomRight B) i hicells
    simp [goal, goalCells]
    change (if c = bottomRight B then 0 else rankExcept (bottomRight B) c + 1) = i + 1
    simp [hc, hrank]

lemma invStat_goal (B : Board) :
    invStat (goal B) = 0 := by
  unfold invStat
  rw [tileList_goal]
  rw [NPuzzle.List.inversionCount_eq_zero_iff_sorted]
  rw [← List.sortedLE_iff_pairwise]
  rw [List.sortedLE_iff_getElem_le_getElem_of_le]
  intro i j hi hj hij
  simp [List.getElem_map, List.getElem_range, hij]

lemma parityClass_goal (B : Board) :
    parityClass (goal B) = targetParity B := by
  by_cases hodd : B.cols % 2 = 1
  · rw [parityClass_of_odd_width (goal B) hodd, targetParity_of_odd_width hodd,
      invStat_goal]
  · have heven : B.cols % 2 = 0 := by
      have hlt := Nat.mod_lt B.cols (by decide : 0 < 2)
      omega
    rw [parityClass_of_even_width (goal B) heven, targetParity_of_even_width heven,
      blank_goal, blankRow_bottomRight, invStat_goal]

/-- If the blank is at `bottomRight` and `tileList` is canonical, the board is `goal`. -/
lemma cfg_eq_goal_of_tileList {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B)
    (ht : tileList cfg = tileList (goal B)) : cfg = goal B := by
  apply config_eq_of_tileList_and_blank cfg (goal B)
  · rw [hbr, blank_goal]
  · exact ht

end NPuzzle.Rect
