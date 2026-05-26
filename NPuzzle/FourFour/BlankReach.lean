import NPuzzle.FourFour
import NPuzzle.FourFour.BlankGrid

namespace NPuzzle.FourFour

/-!
Lift blank grid paths to `Reachable` on full configurations (step 9a).
-/

/-- One legal slide as reachability. -/
lemma reachable_one_step (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) :
    Reachable cfg (slide cfg n h) :=
  Relation.ReflTransGen.single ⟨_, h, rfl⟩

/-- Blank follows one grid edge. -/
lemma reachable_blank_step (cfg : Config) (n : Cell) (hadj : adjacent (blank cfg) n) :
    Reachable cfg (slide cfg n hadj) ∧ blank (slide cfg n hadj) = n :=
  ⟨reachable_one_step cfg n hadj, blank_slide cfg n hadj⟩

/-- Along a `BlankGridPath` from `a`, move the blank from `blank cfg = a` to `t`. -/
lemma reachable_blank_gridPath_start (a : Cell) (cfg : Config) (ha : blank cfg = a)
    (t : Cell) (path : BlankGridPath a t) :
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
lemma reachable_blank_gridPath (cfg : Config) (t : Cell) (path : BlankGridPath (blank cfg) t) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = t :=
  reachable_blank_gridPath_start (blank cfg) cfg rfl t path

/-- Any blank cell is reachable from any configuration (geometry only; tiles may permute). -/
lemma reachable_blank_any (cfg : Config) (t : Cell) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = t :=
  reachable_blank_gridPath cfg t (blankGridPath_any (blank cfg) t)

end NPuzzle.FourFour
