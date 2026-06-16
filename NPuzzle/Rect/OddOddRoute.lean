import NPuzzle.Rect.EvenColumnRoute

namespace NPuzzle.Rect

/-!
Explicit near-full route candidate for odd-by-odd boards.

The route starts with the usual bottom tail, snakes through all nonblank cells
except `cornerUpLeft`, and ends at `cornerUp`.  Closing it through
`bottomRight` gives the near-full cycle shape needed by the odd-by-odd
sufficiency tail.
-/

def oddOddColBeforeRight (B : Board) : Fin B.cols :=
  ⟨B.cols - 2, by
    have hpos := B.cols_pos
    omega⟩

def oddOddMiddleCol {B : Board} (c : Fin (B.cols - 3)) : Fin B.cols :=
  ⟨c.val + 1, by
    have hc := c.isLt
    omega⟩

@[simp]
lemma oddOddColBeforeRight_val {B : Board} :
    (oddOddColBeforeRight B).val = B.cols - 2 :=
  rfl

@[simp]
lemma oddOddMiddleCol_val {B : Board} (c : Fin (B.cols - 3)) :
    (oddOddMiddleCol (B := B) c).val = c.val + 1 :=
  rfl

def oddOddLeftColumn (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 1)).reverse.map fun r =>
    (rowFromRowsMinusOne (B := B) r, colZero B)

def oddOddMiddleColumn (B : Board) (c : Fin (B.cols - 3)) : List (Cell B) :=
  let rows :=
    if (c.val + 1) % 2 = 1 then
      List.finRange (B.rows - 1)
    else
      (List.finRange (B.rows - 1)).reverse
  rows.map fun r =>
    (rowFromRowsMinusOne (B := B) r, oddOddMiddleCol (B := B) c)

def oddOddMiddleSnake (B : Board) : List (Cell B) :=
  (List.finRange (B.cols - 3)).flatMap (oddOddMiddleColumn B)

def oddOddCapRow (B : Board) (r : Fin (B.rows - 2)) : List (Cell B) :=
  let row := rowFromRowsMinusTwo (B := B) r
  if r.val % 2 = 0 then
    [(row, oddOddColBeforeRight B), (row, (bottomRight B).2)]
  else
    [(row, (bottomRight B).2), (row, oddOddColBeforeRight B)]

def oddOddCap (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 2)).flatMap (oddOddCapRow B) ++ [cornerUp B]

def oddOddRouteXs (B : Board) : List (Cell B) :=
  evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B ++ oddOddCap B

lemma oddOddLeftColumn_length (B : Board) :
    (oddOddLeftColumn B).length = B.rows - 1 := by
  simp [oddOddLeftColumn]

lemma oddOddMiddleColumn_length (B : Board) (c : Fin (B.cols - 3)) :
    (oddOddMiddleColumn B c).length = B.rows - 1 := by
  by_cases hpar : (c.val + 1) % 2 = 1 <;>
    simp [oddOddMiddleColumn, hpar]

lemma oddOddMiddleSnake_length (B : Board) :
    (oddOddMiddleSnake B).length = (B.cols - 3) * (B.rows - 1) := by
  simp [oddOddMiddleSnake, oddOddMiddleColumn_length, List.length_flatMap]

lemma oddOddCapRow_length (B : Board) (r : Fin (B.rows - 2)) :
    (oddOddCapRow B r).length = 2 := by
  by_cases hpar : r.val % 2 = 0 <;>
    simp [oddOddCapRow, hpar]

lemma oddOddCap_length (B : Board) :
    (oddOddCap B).length = 2 * (B.rows - 2) + 1 := by
  simp [oddOddCap, oddOddCapRow_length, List.length_flatMap, Nat.mul_comm]

lemma oddOddRoute_length {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    (oddOddRouteXs B).length = B.tileCount - 1 := by
  have hrows_three : 3 ≤ B.rows := by
    omega
  have hcols_three : 3 ≤ B.cols := by
    omega
  have hlen : (oddOddRouteXs B).length + 2 = B.size := by
    simp [oddOddRouteXs, evenColsBottomTail, oddOddLeftColumn_length,
      oddOddMiddleSnake_length, oddOddCap_length, Board.size]
    let r := B.rows
    let c := B.cols
    let cm3 := c - 3
    let cm1 := c - 1
    let rm2 := r - 2
    let rm1 := r - 1
    have hcm3 : cm3 + 3 = c := by omega
    have hcm1 : cm1 + 1 = c := by omega
    have hrm2 : rm2 + 2 = r := by omega
    have hrm1 : rm1 + 1 = r := by omega
    change cm1 + (rm1 + (cm3 * rm1 + (2 * rm2 + 1))) + 2 = r * c
    nlinarith
  rw [Board.tileCount]
  have hsize := B.size_pos
  omega

lemma oddOddCap_ne_nil (B : Board) :
    oddOddCap B ≠ [] := by
  simp [oddOddCap]

lemma oddOddRoute_head {B : Board}
    (hcols : 2 ≤ B.cols) :
    (oddOddRouteXs B).head? = some (cornerLeft B) := by
  have hbottom_ne : evenColsBottomTail B ≠ [] := by
    simp [evenColsBottomTail]
    omega
  have hprefix_ne : evenColsBottomTail B ++ oddOddLeftColumn B ≠ [] := by
    simp [hbottom_ne]
  have hprefix2_ne :
      evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B ≠ [] := by
    simp [hbottom_ne]
  rw [oddOddRouteXs,
    List.head?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B) hprefix2_ne,
    List.head?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B) hprefix_ne,
    List.head?_append_of_ne_nil (evenColsBottomTail B) hbottom_ne]
  simp [evenColsBottomTail, finRange_getLast?_eq_last (by omega : 0 < B.cols - 1),
    cornerLeft, bottomRight, colFromColsMinusOne]

lemma oddOddRoute_getLast {B : Board} :
    (oddOddRouteXs B).getLast? = some (cornerUp B) := by
  rw [oddOddRouteXs,
    List.getLast?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B)
      (oddOddCap_ne_nil B)]
  simp [oddOddCap]

end NPuzzle.Rect
