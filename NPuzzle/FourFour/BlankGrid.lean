import NPuzzle.FourFour

namespace NPuzzle.FourFour

/-!
Blank **geometry** on the 4×4 grid (ignoring tile labels).
Used for step 9 blank-repositioning.
-/

/-- Edge path for the blank on the grid (data, for induction). -/
inductive BlankGridPath : Cell → Cell → Type where
  | nil (c : Cell) : BlankGridPath c c
  | cons {a b c : Cell} (hab : adjacent a b) (rest : BlankGridPath b c) : BlankGridPath a c

namespace BlankGridPath

def transPath {a b c : Cell} (hab : BlankGridPath a b) (hbc : BlankGridPath b c) : BlankGridPath a c :=
  match hab with
  | .nil _ => hbc
  | .cons hab' rest => .cons hab' (transPath rest hbc)

def reverse {a b : Cell} (p : BlankGridPath a b) : BlankGridPath b a :=
  match p with
  | .nil c => .nil c
  | .cons hab rest =>
    transPath (reverse rest) (.cons (adjacent.symm hab) (.nil _))

end BlankGridPath

open BlankGridPath

/-! ### Adjacent moves along the first row and column (building blocks). -/

lemma mkCell_row_col (t : Cell) : mkCell (row t) (col t) = t := by
  fin_cases t <;> simp [mkCell, row, col]

lemma adjacent_mkCell_right0 (r : Fin 4) :
    adjacent (mkCell r 0) (mkCell r 1) := by
  fin_cases r <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

lemma adjacent_mkCell_right1 (r : Fin 4) :
    adjacent (mkCell r 1) (mkCell r 2) := by
  fin_cases r <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

lemma adjacent_mkCell_right2 (r : Fin 4) :
    adjacent (mkCell r 2) (mkCell r 3) := by
  fin_cases r <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

lemma adjacent_mkCell_down0 (c : Fin 4) :
    adjacent (mkCell 0 c) (mkCell 1 c) := by
  fin_cases c <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

lemma adjacent_mkCell_down1 (c : Fin 4) :
    adjacent (mkCell 1 c) (mkCell 2 c) := by
  fin_cases c <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

lemma adjacent_mkCell_down2 (c : Fin 4) :
    adjacent (mkCell 2 c) (mkCell 3 c) := by
  fin_cases c <;> simp [adjacent, sameRow, sameCol, mkCell] <;> omega

def rowPath1 (r : Fin 4) : BlankGridPath (mkCell r 0) (mkCell r 1) :=
  .cons (adjacent_mkCell_right0 r) (.nil _)

def rowPath2 (r : Fin 4) : BlankGridPath (mkCell r 0) (mkCell r 2) :=
  .cons (adjacent_mkCell_right0 r) (.cons (adjacent_mkCell_right1 r) (.nil _))

def rowPath3 (r : Fin 4) : BlankGridPath (mkCell r 0) (mkCell r 3) :=
  .cons (adjacent_mkCell_right0 r)
    (.cons (adjacent_mkCell_right1 r) (.cons (adjacent_mkCell_right2 r) (.nil _)))

/-- Path along row `r` from column `0` to column `c`. -/
def blankGridPath_row (r c : Fin 4) : BlankGridPath (mkCell r 0) (mkCell r c) :=
  match c with
  | ⟨0, _⟩ => .nil _
  | ⟨1, _⟩ => rowPath1 r
  | ⟨2, _⟩ => rowPath2 r
  | ⟨3, _⟩ => rowPath3 r

def colPath1 (c : Fin 4) : BlankGridPath (mkCell 0 c) (mkCell 1 c) :=
  .cons (adjacent_mkCell_down0 c) (.nil _)

def colPath2 (c : Fin 4) : BlankGridPath (mkCell 0 c) (mkCell 2 c) :=
  .cons (adjacent_mkCell_down0 c) (.cons (adjacent_mkCell_down1 c) (.nil _))

def colPath3 (c : Fin 4) : BlankGridPath (mkCell 0 c) (mkCell 3 c) :=
  .cons (adjacent_mkCell_down0 c)
    (.cons (adjacent_mkCell_down1 c) (.cons (adjacent_mkCell_down2 c) (.nil _)))

/-- Path down column `c` from row `0` to row `r`. -/
def blankGridPath_col (r c : Fin 4) : BlankGridPath (mkCell 0 c) (mkCell r c) :=
  match r with
  | ⟨0, _⟩ => .nil _
  | ⟨1, _⟩ => colPath1 c
  | ⟨2, _⟩ => colPath2 c
  | ⟨3, _⟩ => colPath3 c

/-- L-shaped path: `(0,0)` → along row 0 → down column `c` to `(r,c)`. -/
def blankGridPath_corner (r c : Fin 4) : BlankGridPath (mkCell 0 0) (mkCell r c) :=
  transPath (blankGridPath_row 0 c) (blankGridPath_col r c)

/-- Every cell is reachable from `(0,0)` on the grid. -/
def blankGridPath_from_origin (t : Cell) : BlankGridPath (mkCell 0 0) t :=
  cast (by simp [mkCell_row_col]) (blankGridPath_corner (row t) (col t))

/-- Any two cells are connected by a blank grid path. -/
def blankGridPath_any (a b : Cell) : BlankGridPath a b :=
  transPath (reverse (blankGridPath_from_origin a)) (blankGridPath_from_origin b)

end NPuzzle.FourFour
