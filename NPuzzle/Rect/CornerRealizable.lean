import NPuzzle.Rect.CornerPerm
import NPuzzle.Rect.Realizable

namespace NPuzzle.Rect

/-!
The bottom-right corner 3-cycle is realized by the concrete 2x2 blank loop.
-/

private def rankFin {B : Board} (c : Cell B) (hc : c ≠ bottomRight B) : Fin B.tileCount :=
  ⟨rankExcept (bottomRight B) c, by
    rw [← cellsRowMajorExcept_length]
    exact rankExcept_lt hc⟩

private lemma goal_cells_of_ne {B : Board} {c : Cell B} (hc : c ≠ bottomRight B) :
    (goal B).cells c = rankExcept (bottomRight B) c + 1 := by
  simp [goal, goalCells, hc]

private lemma goal_cells_cornerLeft (B : Board) (hcols : 2 ≤ B.cols) :
    (goal B).cells (cornerLeft B) = (cornerLeftIdx B hcols).val + 1 := by
  simp [goal, goalCells, cornerLeftIdx, cornerLeft_ne_bottomRight hcols]

private lemma goal_cells_cornerUpLeft (B : Board) (hrows : 2 ≤ B.rows) :
    (goal B).cells (cornerUpLeft B) = (cornerUpLeftIdx B hrows).val + 1 := by
  simp [goal, goalCells, cornerUpLeftIdx, cornerUpLeft_ne_bottomRight hrows]

private lemma goal_cells_cornerUp (B : Board) (hrows : 2 ≤ B.rows) :
    (goal B).cells (cornerUp B) = (cornerUpIdx B hrows).val + 1 := by
  simp [goal, goalCells, cornerUpIdx, cornerUp_ne_bottomRight hrows]

private lemma rankFin_ne_cornerLeftIdx {B : Board} (hcols : 2 ≤ B.cols)
    {c : Cell B} (hcbr : c ≠ bottomRight B) (hc : c ≠ cornerLeft B) :
    rankFin c hcbr ≠ cornerLeftIdx B hcols := by
  intro h
  apply hc
  have hrank := congrArg Fin.val h
  simp [rankFin, cornerLeftIdx] at hrank
  exact rankExcept_injective hcbr (cornerLeft_ne_bottomRight hcols) hrank

private lemma rankFin_ne_cornerUpLeftIdx {B : Board} (hrows : 2 ≤ B.rows)
    {c : Cell B} (hcbr : c ≠ bottomRight B) (hc : c ≠ cornerUpLeft B) :
    rankFin c hcbr ≠ cornerUpLeftIdx B hrows := by
  intro h
  apply hc
  have hrank := congrArg Fin.val h
  simp [rankFin, cornerUpLeftIdx] at hrank
  exact rankExcept_injective hcbr (cornerUpLeft_ne_bottomRight hrows) hrank

private lemma rankFin_ne_cornerUpIdx {B : Board} (hrows : 2 ≤ B.rows)
    {c : Cell B} (hcbr : c ≠ bottomRight B) (hc : c ≠ cornerUp B) :
    rankFin c hcbr ≠ cornerUpIdx B hrows := by
  intro h
  apply hc
  have hrank := congrArg Fin.val h
  simp [rankFin, cornerUpIdx] at hrank
  exact rankExcept_injective hcbr (cornerUp_ne_bottomRight hrows) hrank

private lemma cornerCycleCells_of_ne {B : Board} (cfg : Config B) {c : Cell B}
    (hbr : c ≠ bottomRight B) (hleft : c ≠ cornerLeft B)
    (hupleft : c ≠ cornerUpLeft B) (hup : c ≠ cornerUp B) :
    cornerCycleCells cfg c = cfg.cells c := by
  simp [cornerCycleCells, swapAt, hbr, hleft, hupleft, hup]

private lemma cornerCycleCfg_cells_of_ne {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbrCfg : blank cfg = bottomRight B) {c : Cell B}
    (hbr : c ≠ bottomRight B) (hleft : c ≠ cornerLeft B)
    (hupleft : c ≠ cornerUpLeft B) (hup : c ≠ cornerUp B) :
    (cornerCycleCfg cfg hrows hcols hbrCfg).cells c = cfg.cells c := by
  rw [cornerCycleCfg_cells_eq cfg hrows hcols hbrCfg]
  exact cornerCycleCells_of_ne cfg hbr hleft hupleft hup

private lemma relabel_cornerPerm_goal_bottomRight (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (relabelConfig (cornerPerm B hrows hcols) (goal B)).cells (bottomRight B) = 0 := by
  simp [relabelConfig, relabelCells, goal, goalCells]

private lemma relabel_cornerPerm_goal_cornerLeft (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (relabelConfig (cornerPerm B hrows hcols) (goal B)).cells (cornerLeft B) =
      (goal B).cells (cornerUpLeft B) := by
  change relabelVal (cornerPerm B hrows hcols) ((goal B).cells (cornerLeft B)) =
    (goal B).cells (cornerUpLeft B)
  rw [goal_cells_cornerLeft B hcols, goal_cells_cornerUpLeft B hrows,
    relabelVal_of_fin, cornerPerm_apply_cornerLeftIdx]

private lemma relabel_cornerPerm_goal_cornerUpLeft (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (relabelConfig (cornerPerm B hrows hcols) (goal B)).cells (cornerUpLeft B) =
      (goal B).cells (cornerUp B) := by
  change relabelVal (cornerPerm B hrows hcols) ((goal B).cells (cornerUpLeft B)) =
    (goal B).cells (cornerUp B)
  rw [goal_cells_cornerUpLeft B hrows, goal_cells_cornerUp B hrows,
    relabelVal_of_fin, cornerPerm_apply_cornerUpLeftIdx]

private lemma relabel_cornerPerm_goal_cornerUp (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (relabelConfig (cornerPerm B hrows hcols) (goal B)).cells (cornerUp B) =
      (goal B).cells (cornerLeft B) := by
  change relabelVal (cornerPerm B hrows hcols) ((goal B).cells (cornerUp B)) =
    (goal B).cells (cornerLeft B)
  rw [goal_cells_cornerUp B hrows, goal_cells_cornerLeft B hcols,
    relabelVal_of_fin, cornerPerm_apply_cornerUpIdx]

private lemma relabel_cornerPerm_goal_of_ne {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) {c : Cell B}
    (hbr : c ≠ bottomRight B) (hleft : c ≠ cornerLeft B)
    (hupleft : c ≠ cornerUpLeft B) (hup : c ≠ cornerUp B) :
    (relabelConfig (cornerPerm B hrows hcols) (goal B)).cells c =
      (goal B).cells c := by
  let x := rankFin c hbr
  have hfixed : cornerPerm B hrows hcols x = x :=
    cornerPerm_apply_of_not_corner hrows hcols
      (rankFin_ne_cornerLeftIdx hcols hbr hleft)
      (rankFin_ne_cornerUpLeftIdx hrows hbr hupleft)
      (rankFin_ne_cornerUpIdx hrows hbr hup)
  have hgoal : (goal B).cells c = x.val + 1 := by
    simp [x, rankFin, goal_cells_of_ne hbr]
  change relabelVal (cornerPerm B hrows hcols) ((goal B).cells c) = (goal B).cells c
  rw [hgoal, relabelVal_of_fin, hfixed]

private lemma permOfCfg_congr_config {B : Board} {cfg cfg' : Config B}
    (hcfg : cfg = cfg') (hbr : blank cfg = bottomRight B)
    (hbr' : blank cfg' = bottomRight B) :
    permOfCfg cfg hbr = permOfCfg cfg' hbr' := by
  subst hcfg
  rfl

lemma cornerCycleCfg_goal_eq_relabel_cornerPerm (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerCycleCfg (goal B) hrows hcols (blank_goal B) =
      relabelConfig (cornerPerm B hrows hcols) (goal B) := by
  apply Config.ext
  intro c
  by_cases hbr : c = bottomRight B
  · subst c
    rw [cornerCycleCfg_cells_bottomRight (goal B) hrows hcols (blank_goal B),
      relabel_cornerPerm_goal_bottomRight B hrows hcols]
  · by_cases hleft : c = cornerLeft B
    · subst c
      rw [cornerCycleCfg_cells_cornerLeft (goal B) hrows hcols (blank_goal B),
        relabel_cornerPerm_goal_cornerLeft B hrows hcols]
    · by_cases hupleft : c = cornerUpLeft B
      · subst c
        rw [cornerCycleCfg_cells_cornerUpLeft (goal B) hrows hcols (blank_goal B),
          relabel_cornerPerm_goal_cornerUpLeft B hrows hcols]
      · by_cases hup : c = cornerUp B
        · subst c
          rw [cornerCycleCfg_cells_cornerUp (goal B) hrows hcols (blank_goal B),
            relabel_cornerPerm_goal_cornerUp B hrows hcols]
        · rw [cornerCycleCfg_cells_of_ne (goal B) hrows hcols (blank_goal B)
            hbr hleft hupleft hup]
          exact (relabel_cornerPerm_goal_of_ne hrows hcols hbr hleft hupleft hup).symm

lemma permOfCfg_cornerCycleCfg_goal (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    permOfCfg (cornerCycleCfg (goal B) hrows hcols (blank_goal B))
      (blank_cornerCycleCfg (goal B) hrows hcols (blank_goal B)) =
        cornerPerm B hrows hcols := by
  let σ := cornerPerm B hrows hcols
  have hcfg : cornerCycleCfg (goal B) hrows hcols (blank_goal B) =
      relabelConfig σ (goal B) :=
    cornerCycleCfg_goal_eq_relabel_cornerPerm B hrows hcols
  have hbrRelabel : blank (relabelConfig σ (goal B)) = bottomRight B := by
    rw [blank_relabelConfig σ (goal B)]
    exact blank_goal B
  rw [permOfCfg_congr_config hcfg
    (blank_cornerCycleCfg (goal B) hrows hcols (blank_goal B)) hbrRelabel]
  have h := permOfCfg_relabel σ (goal B) (blank_goal B)
  simpa [σ, permOfCfg_goal B] using h

lemma cornerPerm_realizable (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    PermRealizable (B := B) (cornerPerm B hrows hcols) :=
  ⟨cornerCycleCfg (goal B) hrows hcols (blank_goal B),
    blank_cornerCycleCfg (goal B) hrows hcols (blank_goal B),
    reachable_cornerCycleCfg (goal B) hrows hcols (blank_goal B),
    permOfCfg_cornerCycleCfg_goal B hrows hcols⟩

end NPuzzle.Rect
