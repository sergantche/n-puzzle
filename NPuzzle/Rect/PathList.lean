import NPuzzle.Rect.PathEffect

namespace NPuzzle.Rect

/-!
Build blank-grid paths from explicit cell lists.

The geometric layer can now specify a candidate route as a list of cells and
prove local adjacency between consecutive entries.  The constructors here turn
that list proof into an actual `BlankGridPath` while preserving the `vertices`
list definitionally enough for later path-effect lemmas.
-/

/-- Successive cells in a list form legal blank-grid steps from the start. -/
def AdjacentChain {B : Board} (a : Cell B) : List (Cell B) → Prop
  | [] => True
  | b :: xs => adjacent a b ∧ AdjacentChain b xs

/-- Endpoint of a nonempty path list is its last cell. -/
@[simp]
lemma listEndpoint_append_singleton {B : Board} (a z : Cell B) (xs : List (Cell B)) :
    listEndpoint a (xs ++ [z]) = z := by
  induction xs generalizing a z with
  | nil => rfl
  | cons x xs ih =>
      exact ih x z

/-- Turn an adjacent cell list into a `BlankGridPath`. -/
def blankGridPathOfList {B : Board} (a t : Cell B) :
    (xs : List (Cell B)) →
    listEndpoint a xs = t →
    AdjacentChain a xs →
    BlankGridPath a t
  | [], hend, _ => by
      cases hend
      exact .nil a
  | b :: xs, hend, hchain =>
      .cons hchain.1 (blankGridPathOfList b t xs hend hchain.2)

@[simp]
lemma vertices_blankGridPathOfList {B : Board} (a t : Cell B)
    (xs : List (Cell B)) (hend : listEndpoint a xs = t)
    (hchain : AdjacentChain a xs) :
    BlankGridPath.vertices (blankGridPathOfList a t xs hend hchain) = xs := by
  induction xs generalizing a with
  | nil =>
      cases hend
      rfl
  | cons b xs ih =>
      simp [blankGridPathOfList, ih]

/-- A closed adjacent list gives a closed `BlankGridPath`. -/
def closedBlankGridPathOfList {B : Board} (a : Cell B) (xs : List (Cell B))
    (hchain : AdjacentChain a (xs ++ [a])) :
    BlankGridPath a a :=
  blankGridPathOfList a a (xs ++ [a]) (listEndpoint_append_singleton a a xs) hchain

@[simp]
lemma vertices_closedBlankGridPathOfList {B : Board} (a : Cell B)
    (xs : List (Cell B)) (hchain : AdjacentChain a (xs ++ [a])) :
    BlankGridPath.vertices (closedBlankGridPathOfList a xs hchain) = xs ++ [a] := by
  simp [closedBlankGridPathOfList]

end NPuzzle.Rect
