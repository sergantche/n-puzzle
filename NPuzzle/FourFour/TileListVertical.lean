import NPuzzle.FourFour

set_option maxHeartbeats 800000

namespace NPuzzle.FourFour

lemma rankExcept_val (skip c : Cell) :
    rankExcept skip c =
      if skip.val < c.val then c.val - 1 else if c.val < skip.val then c.val else 15 := by
  fin_cases skip <;> fin_cases c <;> native_decide

/-- Vertical blank swap reorders `L` by moving one entry (`eraseIdx` / `insertIdx`). -/
lemma tileList_swap_vertical (cells : Cell → ℕ) (b n : Cell)
    (hab : adjacent b n) (hc : sameCol b n) :
    (cellsRowMajorExcept n).map (swapAt cells b n) =
      (((cellsRowMajorExcept b).map cells).eraseIdx (rankExcept b n)).insertIdx (rankExcept n b) (cells n) := by
  fin_cases b <;> fin_cases n <;>
    simp only [adjacent, sameRow, sameCol] at hab hc <;>
    first | contradiction |
      simp [cellsRowMajorExcept, swapAt, List.finRange, List.filter, List.map, rankExcept,
        List.findIdx, List.findIdx.go, List.eraseIdx, List.insertIdx]

lemma rankExcept_vertical_mod (b n : Cell) (hab : adjacent b n) (hc : sameCol b n) :
    (rankExcept b n + rankExcept n b) % 2 = 1 := by
  fin_cases b <;> fin_cases n <;>
    simp only [adjacent, sameRow, sameCol] at hab hc <;>
    first | contradiction |
      simp [rankExcept, cellsRowMajorExcept, List.finRange, List.filter, List.findIdx, List.findIdx.go]

lemma rankExcept_vertical_lt (b n : Cell) (hab : adjacent b n) (hc : sameCol b n) :
    rankExcept b n < 15 ∧ rankExcept n b < 15 := by
  fin_cases b <;> fin_cases n <;>
    simp only [adjacent, sameRow, sameCol] at hab hc <;>
    first | contradiction |
      simp [rankExcept, cellsRowMajorExcept, List.finRange, List.filter, List.findIdx, List.findIdx.go]

lemma cellsRowMajorExcept_blank_slide (cfg : Config) (n : Cell) (hadj : adjacent (blank cfg) n) :
    cellsRowMajorExcept (blank (slide cfg n hadj)) = cellsRowMajorExcept n := by
  rw [blank_slide cfg n hadj]

lemma tileList_slide_vertical (cfg : Config) (n : Cell) (hadj : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    tileList (slide cfg n hadj) =
      let L := tileList cfg
      let b := blank cfg
      let p := rankExcept b n
      let q := rankExcept n b
      L.eraseIdx p |>.insertIdx q (cfg.cells n) := by
  unfold tileList
  rw [blank_slide cfg n hadj]
  dsimp [slide]
  exact tileList_swap_vertical cfg.cells (blank cfg) n hadj hc

end NPuzzle.FourFour