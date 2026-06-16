import NPuzzle.Rect.PathParity

namespace NPuzzle.Rect

/-!
Explicit full-route candidate for two-column boards.

The route goes up the left column, crosses along the top edge, then returns down
the right column to the cell above `bottomRight`.
-/

def colZero (B : Board) : Fin B.cols :=
  ⟨0, B.cols_pos⟩

def colOneOfTwo {B : Board} (hcols : B.cols = 2) : Fin B.cols :=
  ⟨1, by omega⟩

@[simp]
lemma colZero_val {B : Board} :
    (colZero B).val = 0 :=
  rfl

@[simp]
lemma colOneOfTwo_val {B : Board} (hcols : B.cols = 2) :
    (colOneOfTwo hcols).val = 1 :=
  rfl

def rowFromRowsMinusTwo {B : Board} (r : Fin (B.rows - 2)) : Fin B.rows :=
  ⟨r.val, by
    have hr := r.isLt
    omega⟩

@[simp]
lemma rowFromRowsMinusTwo_val {B : Board} (r : Fin (B.rows - 2)) :
    (rowFromRowsMinusTwo (B := B) r).val = r.val :=
  rfl

def rowFromRowsMinusOne {B : Board} (r : Fin (B.rows - 1)) : Fin B.rows :=
  ⟨r.val, by
    have hr := r.isLt
    omega⟩

@[simp]
lemma rowFromRowsMinusOne_val {B : Board} (r : Fin (B.rows - 1)) :
    (rowFromRowsMinusOne (B := B) r).val = r.val :=
  rfl

lemma bottomRight_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    bottomRight B = ((bottomRight B).1, colOneOfTwo hcols) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [bottomRight, colOneOfTwo, hcols]

lemma cornerLeft_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerLeft B = ((bottomRight B).1, colZero B) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerLeft, bottomRight, colZero, hcols]

lemma cornerUpLeft_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerUpLeft B = ((cornerUp B).1, colZero B) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerUpLeft, bottomRight, colZero, hcols]

lemma cornerUp_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerUp B = ((cornerUp B).1, colOneOfTwo hcols) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerUp, bottomRight, colOneOfTwo, hcols]

def twoColumnRouteYs (B : Board) (hcols : B.cols = 2) : List (Cell B) :=
  ((List.finRange (B.rows - 2)).reverse.map fun r =>
      (rowFromRowsMinusTwo (B := B) r, colZero B)) ++
    ((List.finRange (B.rows - 1)).map fun r =>
      (rowFromRowsMinusOne (B := B) r, colOneOfTwo hcols))

lemma twoColumnRoute_nonblank {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ∀ c ∈ cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols,
      c ≠ bottomRight B := by
  intro c hc
  have hcolsLe : 2 ≤ B.cols := by omega
  simp [twoColumnRouteYs] at hc
  rcases hc with hleft | hupleft | htail
  · rw [hleft]
    exact cornerLeft_ne_bottomRight hcolsLe
  · rw [hupleft]
    exact cornerUpLeft_ne_bottomRight hrows
  · rcases htail with htail | htail
    · rcases htail with ⟨r, rfl⟩
      intro h
      have hv := congrArg (fun c : Cell B => c.2.val) h
      simp [bottomRight, colZero, hcols] at hv
    · rcases htail with ⟨r, rfl⟩
      intro h
      have hv := congrArg (fun c : Cell B => c.1.val) h
      have hr := r.isLt
      simp [bottomRight, rowFromRowsMinusOne] at hv
      omega

end NPuzzle.Rect
