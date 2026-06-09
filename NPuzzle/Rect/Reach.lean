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

end NPuzzle.Rect
