import Mathlib.GroupTheory.Perm.List
import NPuzzle.Rect.Reach

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Cell-level effect of running a blank path.

This is the generic replacement for hand-written `hamCells` computations:
following a blank path is the same as repeatedly swapping labels along the
path's edges.
-/

/-- Cell labels after swapping along a blank-grid path starting at `a`. -/
def swapAlongBlankPathStart {B : Board} (cells : Cell B → ℕ) (a : Cell B)
    (t : Cell B) : BlankGridPath a t → Cell B → ℕ
  | .nil _ => cells
  | .cons (b := b) _ rest => swapAlongBlankPathStart (swapAt cells a b) b t rest

/-- Cell labels after swapping from `a` through an explicit list of visited cells. -/
def swapAlongList {B : Board} (cells : Cell B → ℕ) (a : Cell B) :
    List (Cell B) → Cell B → ℕ
  | [] => cells
  | b :: rest => swapAlongList (swapAt cells a b) b rest

/-- The cell permutation induced by following a list from a starting cell. -/
def cellPermAlongList {B : Board} (a : Cell B) : List (Cell B) → Equiv.Perm (Cell B)
  | [] => 1
  | b :: rest => Equiv.swap a b * cellPermAlongList b rest

/-- Current blank location after following an explicit list of visited cells. -/
def listEndpoint {B : Board} (a : Cell B) : List (Cell B) → Cell B
  | [] => a
  | b :: rest => listEndpoint b rest

@[simp]
lemma swapAlongBlankPathStart_nil {B : Board} (cells : Cell B → ℕ) (a : Cell B) :
    swapAlongBlankPathStart cells a a (.nil a) = cells := rfl

@[simp]
lemma swapAlongBlankPathStart_cons {B : Board} (cells : Cell B → ℕ)
    {a b t : Cell B} (hab : adjacent a b) (rest : BlankGridPath b t) :
    swapAlongBlankPathStart cells a t (.cons hab rest) =
      swapAlongBlankPathStart (swapAt cells a b) b t rest := rfl

@[simp]
lemma swapAlongList_nil {B : Board} (cells : Cell B → ℕ) (a : Cell B) :
    swapAlongList cells a [] = cells := rfl

@[simp]
lemma swapAlongList_cons {B : Board} (cells : Cell B → ℕ) (a b : Cell B)
    (rest : List (Cell B)) :
    swapAlongList cells a (b :: rest) = swapAlongList (swapAt cells a b) b rest := rfl

@[simp]
lemma cellPermAlongList_nil {B : Board} (a : Cell B) :
    cellPermAlongList a [] = 1 := rfl

@[simp]
lemma cellPermAlongList_cons {B : Board} (a b : Cell B) (rest : List (Cell B)) :
    cellPermAlongList a (b :: rest) = Equiv.swap a b * cellPermAlongList b rest := rfl

@[simp]
lemma listEndpoint_nil {B : Board} (a : Cell B) :
    listEndpoint a [] = a := rfl

@[simp]
lemma listEndpoint_cons {B : Board} (a b : Cell B) (xs : List (Cell B)) :
    listEndpoint a (b :: xs) = listEndpoint b xs := rfl

lemma swapAlongList_append {B : Board} (cells : Cell B → ℕ)
    (a : Cell B) (xs ys : List (Cell B)) :
    swapAlongList cells a (xs ++ ys) =
      swapAlongList (swapAlongList cells a xs) (listEndpoint a xs) ys := by
  induction xs generalizing cells a with
  | nil => rfl
  | cons x xs ih =>
      simp [ih]

lemma cellPermAlongList_append {B : Board} (a : Cell B)
    (xs ys : List (Cell B)) :
    cellPermAlongList a (xs ++ ys) =
      cellPermAlongList a xs * cellPermAlongList (listEndpoint a xs) ys := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp [ih, mul_assoc]

lemma cellPermAlongList_eq_formPerm_cons {B : Board} (a : Cell B) (xs : List (Cell B)) :
    cellPermAlongList a xs = List.formPerm (a :: xs) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp [ih]

lemma swapAt_eq_apply_swap {B : Board} (cells : Cell B → ℕ) (a b c : Cell B) :
    swapAt cells a b c = cells ((Equiv.swap a b) c) := by
  by_cases hca : c = a
  · subst c
    simp [swapAt]
  · by_cases hcb : c = b
    · subst c
      simp [swapAt, hca]
    · simp [swapAt, hca, hcb, Equiv.swap_apply_of_ne_of_ne]

lemma swapAlongList_eq_cellPermAlongList {B : Board} (cells : Cell B → ℕ)
    (a : Cell B) (xs : List (Cell B)) (c : Cell B) :
    swapAlongList cells a xs c = cells (cellPermAlongList a xs c) := by
  induction xs generalizing cells a c with
  | nil => simp
  | cons b rest ih =>
      calc
        swapAlongList cells a (b :: rest) c =
            swapAlongList (swapAt cells a b) b rest c := rfl
        _ = swapAt cells a b (cellPermAlongList b rest c) :=
            ih (cells := swapAt cells a b) (a := b) (c := c)
        _ = cells ((Equiv.swap a b) (cellPermAlongList b rest c)) :=
            swapAt_eq_apply_swap cells a b (cellPermAlongList b rest c)
        _ = cells (cellPermAlongList a (b :: rest) c) := by
            simp [Equiv.Perm.mul_apply]

lemma swapAlongList_of_not_mem {B : Board} (cells : Cell B → ℕ)
    {a c : Cell B} {xs : List (Cell B)}
    (hca : c ≠ a) (hcxs : c ∉ xs) :
    swapAlongList cells a xs c = cells c := by
  induction xs generalizing cells a with
  | nil => rfl
  | cons b rest ih =>
      have hcb : c ≠ b := by
        intro h
        exact hcxs (by simp [h])
      have hcrest : c ∉ rest := by
        intro h
        exact hcxs (by simp [h])
      rw [swapAlongList_cons]
      rw [ih (cells := swapAt cells a b) (a := b) hcb hcrest]
      exact swapAt_of_ne hca hcb

lemma swapAlongBlankPathStart_eq_swapAlongList {B : Board} (cells : Cell B → ℕ)
    {a t : Cell B} (path : BlankGridPath a t) :
    swapAlongBlankPathStart cells a t path =
      swapAlongList cells a (BlankGridPath.vertices path) := by
  induction path generalizing cells with
  | nil _ => rfl
  | cons hab rest ih => simp [ih]

lemma followBlankGridPathStart_cells {B : Board} (a : Cell B) (cfg : Config B)
    (ha : blank cfg = a) (t : Cell B) (path : BlankGridPath a t) :
    (followBlankGridPathStart a cfg ha t path).cells =
      swapAlongBlankPathStart cfg.cells a t path := by
  match path with
  | .nil _ => rfl
  | .cons (b := b) hab rest =>
      let h : adjacent (blank cfg) b := by
        rw [ha]
        exact hab
      change (followBlankGridPathStart b (slide cfg b h) (blank_slide cfg b h) t rest).cells =
        swapAlongBlankPathStart (swapAt cfg.cells a b) b t rest
      rw [followBlankGridPathStart_cells b (slide cfg b h) (blank_slide cfg b h) t rest]
      congr
      funext c
      change swapAt cfg.cells (blank cfg) b c = swapAt cfg.cells a b c
      rw [ha]

end NPuzzle.Rect
