import Mathlib.GroupTheory.Perm.List
import NPuzzle.Rect.Basic

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Move cell permutations to tile-list indices.

The blank-position-preserving cell permutations are the geometry-facing side of
the proof.  Tile permutations over `Fin B.tileCount` are the group-theory-facing
side.  This file is the conjugation bridge between the two.
-/

/-- Restrict a cell permutation fixing `bottomRight` to nonblank cells. -/
noncomputable def nonblankPermOfCellPerm {B : Board} (π : Equiv.Perm (Cell B))
    (hπ : π (bottomRight B) = bottomRight B) :
    Equiv.Perm {c : Cell B // c ≠ bottomRight B} :=
  π.subtypePerm fun c => by
    constructor
    · intro hπc hc
      exact hπc (by rw [hc, hπ])
    · intro hc hπc
      have hsame : π c = π (bottomRight B) := by
        rw [hπc, hπ]
      exact hc (π.injective hsame)

@[simp]
lemma nonblankPermOfCellPerm_apply_coe {B : Board} (π : Equiv.Perm (Cell B))
    (hπ : π (bottomRight B) = bottomRight B)
    (c : {c : Cell B // c ≠ bottomRight B}) :
    ((nonblankPermOfCellPerm π hπ c).1 : Cell B) = π c.1 := by
  simp [nonblankPermOfCellPerm]

/-- The tile-index permutation induced by a cell permutation fixing `bottomRight`. -/
noncomputable def tilePermOfCellPerm {B : Board} (π : Equiv.Perm (Cell B))
    (hπ : π (bottomRight B) = bottomRight B) :
    Equiv.Perm (Fin B.tileCount) :=
  (nonblankCellEquivFin B).permCongr (nonblankPermOfCellPerm π hπ)

@[simp]
lemma tilePermOfCellPerm_apply {B : Board} (π : Equiv.Perm (Cell B))
    (hπ : π (bottomRight B) = bottomRight B) (i : Fin B.tileCount) :
    tilePermOfCellPerm π hπ i =
      nonblankCellEquivFin B
        (nonblankPermOfCellPerm π hπ ((nonblankCellEquivFin B).symm i)) := rfl

end NPuzzle.Rect
