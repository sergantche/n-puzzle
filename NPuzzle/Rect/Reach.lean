import Mathlib.Data.Nat.Dist
import NPuzzle.Rect.TileInverse

namespace NPuzzle.Rect

/-!
Lift blank grid paths to `Reachable` on rectangular configurations.
-/

/-- A path in the blank-adjacency graph. -/
inductive BlankGridPath {B : Board} : Cell B → Cell B → Type
  | nil (a : Cell B) : BlankGridPath a a
  | cons {a b t : Cell B} (hab : adjacent a b) (rest : BlankGridPath b t) :
      BlankGridPath a t

namespace BlankGridPath

/-- Cells visited after each step of a blank-grid path. -/
def vertices {B : Board} {a b : Cell B} : BlankGridPath a b → List (Cell B)
  | .nil _ => []
  | .cons (b := b) _ rest => b :: vertices rest

@[simp]
lemma vertices_nil {B : Board} (a : Cell B) :
    vertices (.nil a) = [] := rfl

@[simp]
lemma vertices_cons {B : Board} {a b t : Cell B}
    (hab : adjacent a b) (rest : BlankGridPath b t) :
    vertices (.cons hab rest) = b :: vertices rest := rfl

/-- Concatenate blank-grid paths. -/
def append {B : Board} {a b c : Cell B} :
    BlankGridPath a b → BlankGridPath b c → BlankGridPath a c
  | .nil _, q => q
  | .cons hab rest, q => .cons hab (append rest q)

@[simp]
lemma nil_append {B : Board} {a b : Cell B} (p : BlankGridPath a b) :
    append (.nil a) p = p := rfl

@[simp]
lemma append_nil {B : Board} {a b : Cell B} (p : BlankGridPath a b) :
    append p (.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons hab rest ih => simp [append, ih]

@[simp]
lemma append_assoc {B : Board} {a b c d : Cell B}
    (p : BlankGridPath a b) (q : BlankGridPath b c) (r : BlankGridPath c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil _ => rfl
  | cons hab rest ih => simp [append, ih]

@[simp]
lemma vertices_append {B : Board} {a b c : Cell B}
    (p : BlankGridPath a b) (q : BlankGridPath b c) :
    vertices (append p q) = vertices p ++ vertices q := by
  induction p with
  | nil _ => rfl
  | cons hab rest ih => simp [append, ih]

/-- Reverse a blank-grid path. -/
def reverse {B : Board} {a b : Cell B} :
    BlankGridPath a b → BlankGridPath b a
  | .nil a => .nil a
  | .cons hab rest => append (reverse rest) (.cons (adjacent_symm hab) (.nil _))

@[simp]
lemma reverse_nil {B : Board} (a : Cell B) :
    reverse (.nil a) = .nil a := rfl

end BlankGridPath

/-- Any two cells in the same row are connected by a blank-grid path. -/
lemma existsBlankGridPath_row {B : Board} (r : Fin B.rows) (c d : Fin B.cols) :
    Nonempty (BlankGridPath (r, c) (r, d)) := by
  by_cases hcd : c = d
  · subst d
    exact ⟨.nil _⟩
  · by_cases hlt : c.val < d.val
    · let c' : Fin B.cols := ⟨c.val + 1, by omega⟩
      have hdist : Nat.dist c'.val d.val < Nat.dist c.val d.val := by
        simp [c']
        rw [Nat.dist_eq_sub_of_le (Nat.succ_le_of_lt hlt),
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)]
        omega
      rcases existsBlankGridPath_row r c' d with ⟨p⟩
      exact ⟨.cons (adjacent_right r c (by omega)) p⟩
    · have hgt : d.val < c.val := by
        have hvne : c.val ≠ d.val := fun hv => hcd (Fin.ext hv)
        omega
      let c' : Fin B.cols := ⟨c.val - 1, by omega⟩
      have hdist : Nat.dist c'.val d.val < Nat.dist c.val d.val := by
        simp [c']
        rw [Nat.dist_eq_sub_of_le_right (by omega : d.val ≤ c.val - 1),
          Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hgt)]
        omega
      rcases existsBlankGridPath_row r c' d with ⟨p⟩
      exact ⟨.cons (adjacent_left r c (by omega)) p⟩
termination_by Nat.dist c.val d.val

/-- Any two cells in the same column are connected by a blank-grid path. -/
lemma existsBlankGridPath_col {B : Board} (c : Fin B.cols) (r s : Fin B.rows) :
    Nonempty (BlankGridPath (r, c) (s, c)) := by
  by_cases hrs : r = s
  · subst s
    exact ⟨.nil _⟩
  · by_cases hlt : r.val < s.val
    · let r' : Fin B.rows := ⟨r.val + 1, by omega⟩
      have hdist : Nat.dist r'.val s.val < Nat.dist r.val s.val := by
        simp [r']
        rw [Nat.dist_eq_sub_of_le (Nat.succ_le_of_lt hlt),
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)]
        omega
      rcases existsBlankGridPath_col c r' s with ⟨p⟩
      exact ⟨.cons (adjacent_down r c (by omega)) p⟩
    · have hgt : s.val < r.val := by
        have hvne : r.val ≠ s.val := fun hv => hrs (Fin.ext hv)
        omega
      let r' : Fin B.rows := ⟨r.val - 1, by omega⟩
      have hdist : Nat.dist r'.val s.val < Nat.dist r.val s.val := by
        simp [r']
        rw [Nat.dist_eq_sub_of_le_right (by omega : s.val ≤ r.val - 1),
          Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hgt)]
        omega
      rcases existsBlankGridPath_col c r' s with ⟨p⟩
      exact ⟨.cons (adjacent_up r c (by omega)) p⟩
termination_by Nat.dist r.val s.val

/-- A concrete blank-grid path inside one row. -/
noncomputable def blankGridPath_row {B : Board} (r : Fin B.rows) (c d : Fin B.cols) :
    BlankGridPath (r, c) (r, d) :=
  Classical.choice (existsBlankGridPath_row r c d)

/-- A concrete blank-grid path inside one column. -/
noncomputable def blankGridPath_col {B : Board} (c : Fin B.cols) (r s : Fin B.rows) :
    BlankGridPath (r, c) (s, c) :=
  Classical.choice (existsBlankGridPath_col c r s)

/-- L-shaped blank-grid path between any two cells. -/
noncomputable def blankGridPath_any {B : Board} (a b : Cell B) : BlankGridPath a b := by
  rcases a with ⟨ra, ca⟩
  rcases b with ⟨rb, cb⟩
  exact BlankGridPath.append (blankGridPath_row ra ca cb) (blankGridPath_col cb ra rb)

/-- One legal slide as reachability. -/
lemma reachable_one_step {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) :
    Reachable cfg (slide cfg n h) :=
  Relation.ReflTransGen.single ⟨_, h, rfl⟩

/-- Blank follows one grid edge. -/
lemma reachable_blank_step {B : Board} (cfg : Config B) (n : Cell B)
    (hadj : adjacent (blank cfg) n) :
    Reachable cfg (slide cfg n hadj) ∧ blank (slide cfg n hadj) = n :=
  ⟨reachable_one_step cfg n hadj, blank_slide cfg n hadj⟩

/-- Along a `BlankGridPath` from `a`, move the blank from `blank cfg = a` to `t`. -/
lemma reachable_blank_gridPath_start {B : Board} (a : Cell B) (cfg : Config B)
    (ha : blank cfg = a) (t : Cell B) (path : BlankGridPath a t) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = t := by
  match path with
  | .nil _ =>
    subst ha
    exact ⟨cfg, Relation.ReflTransGen.refl, rfl⟩
  | .cons hab rest =>
    have hab' : adjacent (blank cfg) _ := ha.symm ▸ hab
    rcases reachable_blank_gridPath_start _ (slide cfg _ hab') (blank_slide cfg _ hab') _ rest with
      ⟨cfg', hreach, hb⟩
    exact ⟨cfg', Relation.ReflTransGen.trans (reachable_one_step cfg _ hab') hreach, hb⟩

/-- Along a `BlankGridPath`, the blank can be moved from `blank cfg` to `t`. -/
lemma reachable_blank_gridPath {B : Board} (cfg : Config B) (t : Cell B)
    (path : BlankGridPath (blank cfg) t) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = t :=
  reachable_blank_gridPath_start (blank cfg) cfg rfl t path

/-- The blank can be moved to any target cell. -/
lemma reachable_blank_any {B : Board} (cfg : Config B) (t : Cell B) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = t :=
  reachable_blank_gridPath cfg t (blankGridPath_any (blank cfg) t)

end NPuzzle.Rect
