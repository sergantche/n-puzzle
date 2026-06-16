import NPuzzle.Rect.Reach
import NPuzzle.Rect.TileGlue

namespace NPuzzle.Rect

/-!
Degenerate rectangular boards.

If one dimension is `1`, legal moves only slide the blank along a line.  The
relative order of the nonblank tiles never changes, so reachability preserves
the whole `tileList`, not merely its parity statistic.
-/

lemma sameRow_of_rows_eq_one {B : Board} (hrows : B.rows = 1) (a b : Cell B) :
    sameRow a b := by
  apply Fin.ext
  have ha := a.1.isLt
  have hb := b.1.isLt
  omega

lemma sameCol_of_cols_eq_one {B : Board} (hcols : B.cols = 1) (a b : Cell B) :
    sameCol a b := by
  apply Fin.ext
  have ha := a.2.isLt
  have hb := b.2.isLt
  omega

lemma rows_eq_one_of_lt_two {B : Board} (hrows : B.rows < 2) :
    B.rows = 1 := by
  have hpos := B.rows_pos
  omega

lemma cols_eq_one_of_lt_two {B : Board} (hcols : B.cols < 2) :
    B.cols = 1 := by
  have hpos := B.cols_pos
  omega

lemma tileList_slide_horizontal {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    tileList (slide cfg n h) = tileList cfg := by
  rw [tileList_slide_eq_erase_insert cfg n h]
  let L := tileList cfg
  let p := rankExcept (blank cfg) n
  have hp : p < L.length := by
    dsimp [L, p]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h).symm
  have hget : L[p]'hp = cfg.cells n := by
    dsimp [L, p] at hp ⊢
    exact tileList_get_rankExcept cfg n (adjacent_ne h).symm
  have hpne : p ≠ L.length := by omega
  have hpq : rankExcept n (blank cfg) = p := by
    dsimp [p]
    exact (rankExcept_adjacent_horizontal_eq h hr).symm
  rw [hpq]
  rw [← hget, List.insertIdx_eraseIdx_self hpne]
  exact list_set_getElem_eq_self L p hp

lemma tileList_slide_vertical_of_cols_eq_one {B : Board}
    (hcols : B.cols = 1)
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    tileList (slide cfg n h) = tileList cfg := by
  rw [tileList_slide_eq_erase_insert cfg n h]
  let L := tileList cfg
  let p := rankExcept (blank cfg) n
  let q := rankExcept n (blank cfg)
  have hp : p < L.length := by
    dsimp [L, p]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h).symm
  have hq : q < L.length := by
    dsimp [L, q]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h)
  have hget : L[p]'hp = cfg.cells n := by
    dsimp [L, p] at hp ⊢
    exact tileList_get_rankExcept cfg n (adjacent_ne h).symm
  have hdist : Nat.dist p q = 0 := by
    have hdist' : Nat.dist p q = B.cols - 1 := by
      dsimp [p, q]
      exact rankExcept_adjacent_vertical_dist h hc
    omega
  have hpq : p = q := by
    exact Nat.eq_of_dist_eq_zero hdist
  change (L.eraseIdx p).insertIdx q (cfg.cells n) = L
  rw [← hpq]
  rw [← hget, List.insertIdx_eraseIdx_self (Nat.ne_of_lt hp)]
  exact list_set_getElem_eq_self L p hp

lemma tileList_legalStep_of_rows_eq_one {B : Board}
    (hrows : B.rows = 1) {cfg cfg' : Config B}
    (hstep : legalStep cfg cfg') :
    tileList cfg' = tileList cfg := by
  rcases hstep with ⟨n, h, rfl⟩
  exact tileList_slide_horizontal cfg n h (sameRow_of_rows_eq_one hrows _ _)

lemma tileList_legalStep_of_cols_eq_one {B : Board}
    (hcols : B.cols = 1) {cfg cfg' : Config B}
    (hstep : legalStep cfg cfg') :
    tileList cfg' = tileList cfg := by
  rcases hstep with ⟨n, h, rfl⟩
  exact tileList_slide_vertical_of_cols_eq_one hcols cfg n h
    (sameCol_of_cols_eq_one hcols _ _)

lemma tileList_reachable_of_rows_eq_one {B : Board}
    (hrows : B.rows = 1) {cfg cfg' : Config B}
    (hreach : Reachable cfg cfg') :
    tileList cfg' = tileList cfg := by
  induction hreach with
  | refl => rfl
  | tail _ hbc ih =>
      exact (tileList_legalStep_of_rows_eq_one hrows hbc).trans ih

lemma tileList_reachable_of_cols_eq_one {B : Board}
    (hcols : B.cols = 1) {cfg cfg' : Config B}
    (hreach : Reachable cfg cfg') :
    tileList cfg' = tileList cfg := by
  induction hreach with
  | refl => rfl
  | tail _ hbc ih =>
      exact (tileList_legalStep_of_cols_eq_one hcols hbc).trans ih

lemma tileList_reachable_of_rows_lt_two {B : Board}
    (hrows : B.rows < 2) {cfg cfg' : Config B}
    (hreach : Reachable cfg cfg') :
    tileList cfg' = tileList cfg :=
  tileList_reachable_of_rows_eq_one (rows_eq_one_of_lt_two hrows) hreach

lemma tileList_reachable_of_cols_lt_two {B : Board}
    (hcols : B.cols < 2) {cfg cfg' : Config B}
    (hreach : Reachable cfg cfg') :
    tileList cfg' = tileList cfg :=
  tileList_reachable_of_cols_eq_one (cols_eq_one_of_lt_two hcols) hreach

lemma tileList_eq_goal_of_reachable_goal_rows_eq_one {B : Board}
    (hrows : B.rows = 1) {cfg : Config B}
    (hreach : Reachable cfg (goal B)) :
    tileList cfg = tileList (goal B) :=
  (tileList_reachable_of_rows_eq_one hrows hreach).symm

lemma tileList_eq_goal_of_reachable_goal_cols_eq_one {B : Board}
    (hcols : B.cols = 1) {cfg : Config B}
    (hreach : Reachable cfg (goal B)) :
    tileList cfg = tileList (goal B) :=
  (tileList_reachable_of_cols_eq_one hcols hreach).symm

lemma not_reachable_goal_of_rows_eq_one {B : Board}
    (hrows : B.rows = 1) {cfg : Config B}
    (hlist : tileList cfg ≠ tileList (goal B)) :
    ¬ Reachable cfg (goal B) := by
  intro hreach
  exact hlist (tileList_eq_goal_of_reachable_goal_rows_eq_one hrows hreach)

lemma not_reachable_goal_of_cols_eq_one {B : Board}
    (hcols : B.cols = 1) {cfg : Config B}
    (hlist : tileList cfg ≠ tileList (goal B)) :
    ¬ Reachable cfg (goal B) := by
  intro hreach
  exact hlist (tileList_eq_goal_of_reachable_goal_cols_eq_one hcols hreach)

lemma not_reachable_goal_of_rows_lt_two {B : Board}
    (hrows : B.rows < 2) {cfg : Config B}
    (hlist : tileList cfg ≠ tileList (goal B)) :
    ¬ Reachable cfg (goal B) :=
  not_reachable_goal_of_rows_eq_one (rows_eq_one_of_lt_two hrows) hlist

lemma not_reachable_goal_of_cols_lt_two {B : Board}
    (hcols : B.cols < 2) {cfg : Config B}
    (hlist : tileList cfg ≠ tileList (goal B)) :
    ¬ Reachable cfg (goal B) :=
  not_reachable_goal_of_cols_eq_one (cols_eq_one_of_lt_two hcols) hlist

lemma reachable_goal_of_tileList_rows_eq_one {B : Board}
    (hrows : B.rows = 1) {cfg : Config B}
    (hlist : tileList cfg = tileList (goal B)) :
    Reachable cfg (goal B) := by
  rcases reachable_blank_any cfg (bottomRight B) with ⟨cfg', hreach, hbr⟩
  have hlist' : tileList cfg' = tileList (goal B) :=
    (tileList_reachable_of_rows_eq_one hrows hreach).trans hlist
  exact Relation.ReflTransGen.trans hreach
    (reachable_goal_of_tileList cfg' hbr hlist')

lemma reachable_goal_of_tileList_cols_eq_one {B : Board}
    (hcols : B.cols = 1) {cfg : Config B}
    (hlist : tileList cfg = tileList (goal B)) :
    Reachable cfg (goal B) := by
  rcases reachable_blank_any cfg (bottomRight B) with ⟨cfg', hreach, hbr⟩
  have hlist' : tileList cfg' = tileList (goal B) :=
    (tileList_reachable_of_cols_eq_one hcols hreach).trans hlist
  exact Relation.ReflTransGen.trans hreach
    (reachable_goal_of_tileList cfg' hbr hlist')

lemma reachable_goal_of_tileList_rows_lt_two {B : Board}
    (hrows : B.rows < 2) {cfg : Config B}
    (hlist : tileList cfg = tileList (goal B)) :
    Reachable cfg (goal B) :=
  reachable_goal_of_tileList_rows_eq_one (rows_eq_one_of_lt_two hrows) hlist

lemma reachable_goal_of_tileList_cols_lt_two {B : Board}
    (hcols : B.cols < 2) {cfg : Config B}
    (hlist : tileList cfg = tileList (goal B)) :
    Reachable cfg (goal B) :=
  reachable_goal_of_tileList_cols_eq_one (cols_eq_one_of_lt_two hcols) hlist

theorem solvability_rows_eq_one {B : Board}
    (hrows : B.rows = 1) (cfg : Config B) :
    Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B) := by
  constructor
  · exact tileList_eq_goal_of_reachable_goal_rows_eq_one hrows
  · exact reachable_goal_of_tileList_rows_eq_one hrows

theorem solvability_cols_eq_one {B : Board}
    (hcols : B.cols = 1) (cfg : Config B) :
    Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B) := by
  constructor
  · exact tileList_eq_goal_of_reachable_goal_cols_eq_one hcols
  · exact reachable_goal_of_tileList_cols_eq_one hcols

theorem solvability_rows_lt_two {B : Board}
    (hrows : B.rows < 2) (cfg : Config B) :
    Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B) :=
  solvability_rows_eq_one (rows_eq_one_of_lt_two hrows) cfg

theorem solvability_cols_lt_two {B : Board}
    (hcols : B.cols < 2) (cfg : Config B) :
    Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B) :=
  solvability_cols_eq_one (cols_eq_one_of_lt_two hcols) cfg

end NPuzzle.Rect
