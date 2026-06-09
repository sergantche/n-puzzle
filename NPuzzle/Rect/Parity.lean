import Mathlib.Tactic
import NPuzzle.List.Inversion
import NPuzzle.Rect.Config

namespace NPuzzle.Rect

/-!
Parameterized parity data for rectangular boards.

This matches the README criterion:
* odd width: inversion parity only;
* even width: inversion parity plus blank row counted from the bottom.
-/

/-- Blank row counted from the bottom; bottom row has value `1`. -/
def blankRowFromBottom {B : Board} (b : Cell B) : ℕ :=
  B.rows - b.1.val

lemma blankRow_bottomRight (B : Board) :
    blankRowFromBottom (bottomRight B) = 1 := by
  unfold blankRowFromBottom bottomRight
  simp
  have h := B.rows_pos
  omega

/-- `I(L)` for a rectangular configuration. -/
noncomputable def invStat {B : Board} (cfg : Config B) : ℕ :=
  NPuzzle.List.inversionCount (tileList cfg)

/-- The README parity statistic for rectangular boards. -/
noncomputable def parityClass {B : Board} (cfg : Config B) : ℕ :=
  if B.cols % 2 = 1 then
    invStat cfg % 2
  else
    (invStat cfg + blankRowFromBottom (blank cfg)) % 2

/-- The target parity value for the standard bottom-right goal. -/
def targetParity (B : Board) : ℕ :=
  if B.cols % 2 = 1 then 0 else 1

noncomputable def parityClassGoal (B : Board) : ℕ :=
  parityClass (goal B)

lemma parityClass_of_odd_width {B : Board} (cfg : Config B) (hodd : B.cols % 2 = 1) :
    parityClass cfg = invStat cfg % 2 := by
  simp [parityClass, hodd]

lemma parityClass_of_even_width {B : Board} (cfg : Config B) (heven : B.cols % 2 = 0) :
    parityClass cfg = (invStat cfg + blankRowFromBottom (blank cfg)) % 2 := by
  have hnot : B.cols % 2 ≠ 1 := by omega
  simp [parityClass, hnot]

lemma targetParity_of_odd_width {B : Board} (hodd : B.cols % 2 = 1) :
    targetParity B = 0 := by
  simp [targetParity, hodd]

lemma targetParity_of_even_width {B : Board} (heven : B.cols % 2 = 0) :
    targetParity B = 1 := by
  have hnot : B.cols % 2 ≠ 1 := by omega
  simp [targetParity, hnot]

lemma parityClass_lt_two {B : Board} (cfg : Config B) : parityClass cfg < 2 := by
  unfold parityClass
  split <;> exact Nat.mod_lt _ (by decide)

lemma targetParity_lt_two (B : Board) : targetParity B < 2 := by
  unfold targetParity
  split <;> omega

end NPuzzle.Rect
