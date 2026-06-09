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

lemma permCongr_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ τ : Equiv.Perm α) :
    e.permCongr (σ * τ) = e.permCongr σ * e.permCongr τ := by
  ext x
  simp [Equiv.Perm.mul_apply]

lemma permCongr_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) :
    e.permCongr (1 : Equiv.Perm α) = 1 := by
  ext x
  simp

lemma permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y : α) :
    e.permCongr (Equiv.swap x y) = Equiv.swap (e x) (e y) := by
  ext z
  by_cases hzex : z = e x
  · subst z
    simp
  · by_cases hzey : z = e y
    · subst z
      simp
    · have hsx : e.symm z ≠ x := by
        intro h
        exact hzex (by simpa using congrArg e h)
      have hsy : e.symm z ≠ y := by
        intro h
        exact hzey (by simpa using congrArg e h)
      simp [Equiv.swap_apply_def, hzex, hzey, hsx, hsy]

lemma permCongr_formPerm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (xs : List α) :
    e.permCongr (List.formPerm xs) = List.formPerm (xs.map e) := by
  induction xs with
  | nil => exact permCongr_one e
  | cons x xs ih =>
      cases xs with
      | nil => exact permCongr_one e
      | cons y ys =>
          simp [permCongr_swap, ih]

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
