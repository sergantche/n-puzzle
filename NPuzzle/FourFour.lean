/-
### 4×4 sliding puzzle (15-puzzle)

Grid, configurations, goal state, row-major tile list, inversion count `I(L)`,
`r_B`, and `(I(L) + r_B) mod 2` per the README “Target theorem”.

The main proof is still open (`solvability_four_four`).
-/

import Mathlib.Data.List.FinRange
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

namespace NPuzzle.FourFour

/-!
## Encoding of the 4×4 grid

Cells are indexed **row-major**: indices `0…15` run left→right along row `0`, then row `1`, …
So `(row i, col j)` ↔ linear index `4*i + j`.
-/

/-- Linear cell index `0…15`. -/
abbrev Cell : Type := Fin 16

/-- Row from the **top**, values `0…3`. Same as README row index minus `1`. -/
def row (c : Cell) : Fin 4 :=
  ⟨(c.val / 4 : ℕ), by omega⟩

/-- Column from the **left**, values `0…3`. -/
def col (c : Cell) : Fin 4 :=
  ⟨(c.val % 4 : ℕ), by omega⟩

/-- Inverse of `row`/`col`: build cell `⟨r,c⟩`. -/
def mkCell (r c : Fin 4) : Cell :=
  ⟨(r.val * 4 + c.val : ℕ), by omega⟩

/-- Reading back the row after packing `(r,c)` into a linear cell index. -/
@[simp] lemma row_mkCell (r c : Fin 4) : row (mkCell r c) = r := by
  fin_cases r <;> fin_cases c <;> rfl

/-- Reading back the column after packing `(r,c)`. -/
@[simp] lemma col_mkCell (r c : Fin 4) : col (mkCell r c) = c := by
  fin_cases r <;> fin_cases c <;> rfl

/-! ### Graph neighbours (legal-slide geometry only).

Horizontally: same row, column indices differ by `1`.
Vertically: same column, linear index differs by `4` (width of the board).
-/

def sameRow (a b : Cell) : Prop :=
  a.val / 4 = b.val / 4

def sameCol (a b : Cell) : Prop :=
  a.val % 4 = b.val % 4

/-- Edge-adjacent cells (a legal slide always swaps the blank across such a pair). -/
def adjacent (a b : Cell) : Prop :=
  (sameRow a b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)) ∨
  (sameCol a b ∧ (a.val + 4 = b.val ∨ b.val + 4 = a.val))

lemma adjacent.symm {a b : Cell} (h : adjacent a b) : adjacent b a := by
  rcases h with (⟨hr, hror⟩ | ⟨hc, hcor⟩)
  · exact Or.inl ⟨by simpa [sameRow, eq_comm] using hr, Or.symm hror⟩
  · exact Or.inr ⟨by simpa [sameCol, eq_comm] using hc, Or.symm hcor⟩

lemma adjacent.ne {a b : Cell} (h : adjacent a b) : a ≠ b := by
  rintro rfl
  rcases h with (⟨_, hror⟩ | ⟨_, hcor⟩)
  · rcases hror with h | h <;> omega
  · rcases hcor with h | h <;> omega

/-! ### Configurations

Labels: `0` = blank, `1…15` = tiles (README uses `1…NM-1`).
-/

/-- Predicate “full labeling”: one blank, each tile once, values bounded by `15`. -/
def IsValid (cells : Cell → ℕ) : Prop :=
  (∀ i, cells i ≤ 15) ∧
  (∃! b : Cell, cells b = 0) ∧
  (∀ k : ℕ, 1 ≤ k ∧ k ≤ 15 → ∃! i : Cell, cells i = k)

structure Config where
  cells : Cell → ℕ
  valid : IsValid cells

/-! ### Goal board (README).

Tiles `1…15` along cells `0…14`, blank at bottom-right cell `15`.
-/

def goalCells (i : Cell) : ℕ :=
  if i.val < 15 then i.val + 1 else 0

/-! ### Row-major list `L` and inversion count `I(L)`

`cellsRowMajorExcept b`: all cells in increasing linear order **except** the blank cell `b`.
Then map labels → this is the README sequence `L` for that blank position.

For a **horizontal** slide the multiset/order of values in `L` stays the same (lemma TODO);
vertical slides permute `L` and can change `inversionCount`.
-/

def cellsRowMajorExcept (b : Cell) : List Cell :=
  (List.finRange 16).filter (· ≠ b)

/-- Pair-inversion count for a list of natural numbers (definition matches README). -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if x > y then 1 else 0) 0 + inversionCount xs

/-- Canonical blank cell from `∃!` in `IsValid` (noncomputable choice). -/
noncomputable def blank (cfg : Config) : Cell :=
  Classical.choose (ExistsUnique.exists cfg.valid.2.1)

lemma blank_zero (cfg : Config) : cfg.cells (blank cfg) = 0 :=
  Classical.choose_spec (ExistsUnique.exists cfg.valid.2.1)

/-- Bottom-right cell (goal blank). -/
def bottomRight : Cell := ⟨15, by omega⟩

/-- Swap labels at cells `a` and `b`. -/
def swapAt (cells : Cell → ℕ) (a b : Cell) : Cell → ℕ :=
  fun c =>
    if c = a then cells b
    else if c = b then cells a
    else cells c

lemma swapAt_le {cells : Cell → ℕ} (h : ∀ i, cells i ≤ 15) (a b : Cell) (i : Cell) :
    swapAt cells a b i ≤ 15 := by
  simp only [swapAt]
  split_ifs <;> exact h _

lemma swapAt_a {cells : Cell → ℕ} {a b : Cell} (hne : a ≠ b) :
    swapAt cells a b a = cells b := by
  dsimp [swapAt]
  simp [hne.symm]

lemma swapAt_b {cells : Cell → ℕ} {a b : Cell} (hne : a ≠ b) (ha0 : cells a = 0) :
    swapAt cells a b b = 0 := by
  dsimp [swapAt]
  by_cases h : b = a <;> simp [h, ha0]

lemma swapAt_of_ne {cells : Cell → ℕ} {a b c : Cell} (hca : c ≠ a) (hcb : c ≠ b) :
    swapAt cells a b c = cells c := by
  dsimp [swapAt]
  simp [hca, hcb]

lemma tile_ne_zero_of_ne_blank {cells : Cell → ℕ} (hv : IsValid cells) {a b : Cell}
    (ha0 : cells a = 0) (hne : a ≠ b) : cells b ≠ 0 := by
  intro h0
  exact hne (ExistsUnique.unique hv.2.1 h0 ha0).symm

lemma swapAt_valid {cells : Cell → ℕ} (hv : IsValid cells) (a b : Cell)
    (ha0 : cells a = 0) (hne : a ≠ b) : IsValid (swapAt cells a b) := by
  rcases hv with ⟨hle, ⟨b0, hb0, huniq0⟩, htiles⟩
  have hv' : IsValid cells := ⟨hle, ⟨b0, hb0, huniq0⟩, htiles⟩
  have hbne0 := tile_ne_zero_of_ne_blank hv' ha0 hne
  constructor
  · exact swapAt_le hle a b
  constructor
  · refine ExistsUnique.intro b (swapAt_b hne ha0) ?_
    intro c hc0
    dsimp [swapAt] at hc0
    by_cases hca : c = a <;> by_cases hcb : c = b
    · exact absurd (hca.symm ▸ hcb) hne
    · simp [hca, hcb, hne] at hc0
      exact (hbne0 hc0).elim
    · exact hcb
    · simp [hca, hcb] at hc0
      have hc' : c = a := ExistsUnique.unique ⟨b0, hb0, huniq0⟩ hc0 ha0
      exact absurd hc' hca
  · intro k hk
    rcases htiles k hk with ⟨i, hi, huniq⟩
    have hia : i ≠ a := by
      rintro rfl
      rw [ha0] at hi
      omega
    refine ExistsUnique.intro (if i = b then a else i) ?_ ?_
    · by_cases hib : i = b
      · dsimp [swapAt]
        simp [hib, hne, ha0]
        rw [hib] at hi
        exact hi
      · dsimp [swapAt]
        simp [hib, hia]
        exact hi
    · intro j hj
      by_cases hja : j = a
      · by_cases hjb : j = b
        · exact absurd (hja.symm ▸ hjb) hne
        · dsimp [swapAt] at hj ⊢
          simp [hja, hjb, hne] at hj ⊢
          subst hja
          have hib : i = b := (huniq b hj).symm
          simp [hib]
      · by_cases hjb : j = b
        · have h0 : 0 = k := by
            rw [hjb, swapAt_b hne ha0] at hj
            exact hj
          rcases hk with ⟨_, hkpos⟩
          omega
        · dsimp [swapAt] at hj
          simp [hja, hjb] at hj
          have hij : j = i := huniq j hj
          by_cases hib : i = b
          · have hjib : j = b := Eq.trans hij hib
            exact absurd hjib hjb
          · simp [hib, hij]

/-- One legal move: slide the blank into adjacent cell `n`. -/
noncomputable def slide (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) : Config :=
  { cells := swapAt cfg.cells (blank cfg) n
    valid := swapAt_valid cfg.valid (blank cfg) n (blank_zero cfg) (adjacent.ne h) }

/-- `cfg'` is one legal move away from `cfg`. -/
def legalStep (cfg cfg' : Config) : Prop :=
  ∃ n : Cell, ∃ h : adjacent (blank cfg) n, cfg' = slide cfg n h

/-- Reachability via legal moves. -/
def Reachable : Config → Config → Prop :=
  Relation.ReflTransGen legalStep

/-- README tile list `L` for `cfg`. -/
noncomputable def tileList (cfg : Config) : List ℕ :=
  (cellsRowMajorExcept (blank cfg)).map cfg.cells

/-- `I(L)` for `cfg`. -/
noncomputable def invStat (cfg : Config) : ℕ :=
  inversionCount (tileList cfg)

/-!
### Blank row from bottom `r_B` (fixed `N = 4`)

README 1-based row from top: `i_b ∈ {1,…,4}`.
Here `row c ∈ {0,…,3}` is 0-based from top, so `r_B = 4 - row.val`
matches `r_B = N - i_b + 1` with `N = 4`.
-/

def blankRowFromBottom (b : Cell) : ℕ :=
  4 - (row b).val

/-!
### Parity class `(I(L) + r_B) mod 2`

Matches the README target theorem for **even** width `M`: compare to goal (`≡ 1` for standard goal).
-/

noncomputable def parityClass (cfg : Config) : ℕ :=
  (invStat cfg + blankRowFromBottom (blank cfg)) % 2

/-! ### Goal as a `Config` -/

lemma goalCells_eq_zero (b : Cell) : goalCells b = 0 ↔ b = bottomRight := by
  fin_cases b <;> simp [goalCells, bottomRight] <;> omega

lemma goalCells_eq_k {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 15) (i : Cell) :
    goalCells i = k ↔ i = ⟨(k - 1), by omega⟩ := by
  constructor
  · intro h
    have hlt : i.val < 15 := by
      dsimp [goalCells] at h
      split_ifs at h <;> omega
    have hval : i.val = k - 1 := by
      dsimp [goalCells] at h
      split_ifs at h <;> omega
    ext
    exact hval
  · rintro rfl
    have hlt : (k - 1) < 15 := by omega
    dsimp [goalCells]
    simp [hlt]
    omega

lemma goal_ex_unique_blank : ∃! b : Cell, goalCells b = 0 := by
  refine ⟨bottomRight, by simp [goalCells, bottomRight], ?_⟩
  intro b hb
  exact (goalCells_eq_zero b).mp hb

lemma goal_ex_unique_labels {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 15) :
    ∃! i : Cell, goalCells i = k := by
  refine ⟨⟨k - 1, by omega⟩, ?_, ?_⟩
  · have hlt : (k - 1) < 15 := by omega
    dsimp [goalCells]
    simp [hlt]
    omega
  · intro i hi
    exact (goalCells_eq_k hk i).mp hi

lemma goalCells_le (i : Cell) : goalCells i ≤ 15 := by
  dsimp [goalCells]; split_ifs <;> omega

/-- Package `goalCells` + proofs into `Config`. -/
def goal : Config :=
  ⟨goalCells,
    ⟨goalCells_le,
      goal_ex_unique_blank,
      fun _ hk => goal_ex_unique_labels hk⟩⟩

lemma blank_goal : blank goal = bottomRight := by
  apply ExistsUnique.unique goal.valid.2.1
  · exact blank_zero goal
  · change goalCells bottomRight = 0
    simp [goalCells, bottomRight]

/-- Parity statistic evaluated at `goal`. -/
noncomputable def parityClassGoal : ℕ :=
  parityClass goal

end NPuzzle.FourFour
