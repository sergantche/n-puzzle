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

/-- Repackage a list of nonblank cells as a list in the nonblank-cell subtype. -/
def nonblankSubtypeList {B : Board} (xs : List (Cell B))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    List {c : Cell B // c ≠ bottomRight B} :=
  xs.pmap (fun c hc => ⟨c, hc⟩) hxs

@[simp]
lemma nonblankSubtypeList_map_val {B : Board} (xs : List (Cell B))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    (nonblankSubtypeList xs hxs).map (fun c => c.1) = xs := by
  unfold nonblankSubtypeList
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih]

lemma ofSubtype_swap {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    (x y : Subtype p) :
    Equiv.Perm.ofSubtype (Equiv.swap x y) = Equiv.swap x.1 y.1 := by
  apply Equiv.ext
  intro z
  by_cases hz : p z
  · rw [Equiv.Perm.ofSubtype_apply_of_mem (Equiv.swap x y) hz]
    by_cases hzx : z = x.1
    · subst z
      simp
    · by_cases hzy : z = y.1
      · subst z
        simp
      · have hsx : (⟨z, hz⟩ : Subtype p) ≠ x := by
          intro h
          exact hzx (congrArg Subtype.val h)
        have hsy : (⟨z, hz⟩ : Subtype p) ≠ y := by
          intro h
          exact hzy (congrArg Subtype.val h)
        simp [Equiv.swap_apply_of_ne_of_ne hsx hsy,
          Equiv.swap_apply_of_ne_of_ne hzx hzy]
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (Equiv.swap x y) hz]
    have hzx : z ≠ x.1 := by
      intro h
      exact hz (h.symm ▸ x.2)
    have hzy : z ≠ y.1 := by
      intro h
      exact hz (h.symm ▸ y.2)
    exact (Equiv.swap_apply_of_ne_of_ne hzx hzy).symm

lemma ofSubtype_formPerm_nonblankSubtypeList {B : Board} (xs : List (Cell B))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    Equiv.Perm.ofSubtype (List.formPerm (nonblankSubtypeList xs hxs)) =
      List.formPerm xs := by
  induction xs with
  | nil => simp [nonblankSubtypeList]
  | cons x xs ih =>
      cases xs with
      | nil => simp [nonblankSubtypeList]
      | cons y ys =>
          have hx : x ≠ bottomRight B := hxs x (by simp)
          have hy : y ≠ bottomRight B := hxs y (by simp)
          have htail : ∀ c ∈ y :: ys, c ≠ bottomRight B := by
            intro c hc
            exact hxs c (by simp [hc])
          have hys : ∀ c ∈ ys, c ≠ bottomRight B := by
            intro c hc
            exact htail c (by simp [hc])
          have hlist :
              nonblankSubtypeList (x :: y :: ys) hxs =
                (⟨x, hx⟩ : {c : Cell B // c ≠ bottomRight B}) ::
                  nonblankSubtypeList (y :: ys) htail := by
            simp [nonblankSubtypeList]
          have htailList :
              nonblankSubtypeList (y :: ys) htail =
                (⟨y, hy⟩ : {c : Cell B // c ≠ bottomRight B}) ::
                  nonblankSubtypeList ys hys := by
            simp [nonblankSubtypeList]
          rw [hlist, htailList, List.formPerm_cons_cons, map_mul, ofSubtype_swap]
          rw [← htailList, ih htail]
          simp [List.formPerm_cons_cons]

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

lemma tilePermOfCellPerm_irrel {B : Board} (π : Equiv.Perm (Cell B))
    (h₁ h₂ : π (bottomRight B) = bottomRight B) :
    tilePermOfCellPerm π h₁ = tilePermOfCellPerm π h₂ := by
  have h : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst h
  rfl

lemma tilePermOfCellPerm_congr_perm {B : Board}
    {π τ : Equiv.Perm (Cell B)}
    (hπτ : π = τ)
    (hπ : π (bottomRight B) = bottomRight B)
    (hτ : τ (bottomRight B) = bottomRight B) :
    tilePermOfCellPerm π hπ = tilePermOfCellPerm τ hτ := by
  subst hπτ
  exact tilePermOfCellPerm_irrel _ hπ hτ

lemma ofSubtype_fix_bottomRight {B : Board}
    (σ : Equiv.Perm {c : Cell B // c ≠ bottomRight B}) :
    Equiv.Perm.ofSubtype σ (bottomRight B) = bottomRight B :=
  Equiv.Perm.ofSubtype_apply_of_not_mem σ (by intro h; exact h rfl)

lemma nonblankPermOfCellPerm_ofSubtype {B : Board}
    (σ : Equiv.Perm {c : Cell B // c ≠ bottomRight B})
    (hfix : Equiv.Perm.ofSubtype σ (bottomRight B) = bottomRight B) :
    nonblankPermOfCellPerm (Equiv.Perm.ofSubtype σ) hfix = σ := by
  apply Equiv.ext
  intro c
  apply Subtype.ext
  simp [nonblankPermOfCellPerm]

lemma tilePermOfCellPerm_ofSubtype_formPerm {B : Board}
    (xs : List {c : Cell B // c ≠ bottomRight B}) :
    tilePermOfCellPerm (Equiv.Perm.ofSubtype (List.formPerm xs))
        (ofSubtype_fix_bottomRight (List.formPerm xs)) =
      List.formPerm (xs.map (nonblankCellEquivFin B)) := by
  unfold tilePermOfCellPerm
  rw [nonblankPermOfCellPerm_ofSubtype]
  exact permCongr_formPerm (nonblankCellEquivFin B) xs

end NPuzzle.Rect
