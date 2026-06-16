import NPuzzle.Rect.EvenDimension
import NPuzzle.Rect.Thin

namespace NPuzzle.Rect

/-!
Top-level rectangular solvability dispatchers.

Boards with both dimensions at least `2` use the usual parity criterion.
Thin boards use the stronger one-dimensional invariant: the whole `tileList`
is preserved.
-/

theorem solvability_thin {B : Board}
    (hthin : B.rows < 2 ∨ B.cols < 2) (cfg : Config B) :
    Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B) := by
  rcases hthin with hrows | hcols
  · exact solvability_rows_lt_two hrows cfg
  · exact solvability_cols_lt_two hcols cfg

theorem solvability_fat {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) (cfg : Config B) :
    Reachable cfg (goal B) ↔ parityClass cfg = parityClass (goal B) :=
  solvability_of_two_le hrows hcols cfg

theorem solvability_rectangular {B : Board} (cfg : Config B) :
    (if 2 ≤ B.rows ∧ 2 ≤ B.cols then
        Reachable cfg (goal B) ↔ parityClass cfg = parityClass (goal B)
      else
        Reachable cfg (goal B) ↔ tileList cfg = tileList (goal B)) := by
  by_cases h : 2 ≤ B.rows ∧ 2 ≤ B.cols
  · simpa [h] using solvability_fat h.1 h.2 cfg
  · have hthin : B.rows < 2 ∨ B.cols < 2 := by
      omega
    simpa [h] using solvability_thin hthin cfg

end NPuzzle.Rect
