import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Relation
import Mathlib.Tactic
import NPuzzle.Rect.Basic

namespace NPuzzle.Rect

/-!
Parameterized rectangular puzzle configurations.

This is the board-generic analogue of the first half of `NPuzzle.FourFour`:
labels are natural numbers, `0` is the blank, and `1..B.tileCount` are the
nonblank tiles.
-/

/-- Predicate “full labeling”: one blank, each tile once, values bounded by `B.tileCount`. -/
def IsValid (B : Board) (cells : Cell B → ℕ) : Prop :=
  (∀ i, cells i ≤ B.tileCount) ∧
  (∃! b : Cell B, cells b = 0) ∧
  (∀ k : ℕ, 1 ≤ k ∧ k ≤ B.tileCount → ∃! i : Cell B, cells i = k)

structure Config (B : Board) where
  cells : Cell B → ℕ
  valid : IsValid B cells

@[ext]
theorem Config.ext {B : Board} {cfg cfg' : Config B}
    (h : ∀ c, cfg.cells c = cfg'.cells c) : cfg = cfg' := by
  rcases cfg with ⟨cells, valid⟩
  rcases cfg' with ⟨cells', valid'⟩
  have hcells : cells = cells' := funext h
  subst hcells
  rfl

/-- Canonical blank cell from `∃!` in `IsValid` (noncomputable choice). -/
noncomputable def blank {B : Board} (cfg : Config B) : Cell B :=
  Classical.choose (ExistsUnique.exists cfg.valid.2.1)

lemma blank_zero {B : Board} (cfg : Config B) : cfg.cells (blank cfg) = 0 :=
  Classical.choose_spec (ExistsUnique.exists cfg.valid.2.1)

/-- Swap labels at cells `a` and `b`. -/
def swapAt {B : Board} (cells : Cell B → ℕ) (a b : Cell B) : Cell B → ℕ :=
  fun c =>
    if c = a then cells b
    else if c = b then cells a
    else cells c

lemma swapAt_le {B : Board} {cells : Cell B → ℕ}
    (h : ∀ i, cells i ≤ B.tileCount) (a b : Cell B) (i : Cell B) :
    swapAt cells a b i ≤ B.tileCount := by
  simp only [swapAt]
  split_ifs <;> exact h _

lemma swapAt_a {B : Board} {cells : Cell B → ℕ} {a b : Cell B} :
    swapAt cells a b a = cells b := by
  dsimp [swapAt]
  simp

lemma swapAt_b {B : Board} {cells : Cell B → ℕ} {a b : Cell B}
    (ha0 : cells a = 0) :
    swapAt cells a b b = 0 := by
  dsimp [swapAt]
  by_cases h : b = a <;> simp [h, ha0]

lemma swapAt_of_ne {B : Board} {cells : Cell B → ℕ} {a b c : Cell B}
    (hca : c ≠ a) (hcb : c ≠ b) :
    swapAt cells a b c = cells c := by
  dsimp [swapAt]
  simp [hca, hcb]

lemma swapAt_swapAt {B : Board} {cells : Cell B → ℕ} {a b : Cell B} (hne : a ≠ b) :
    swapAt (swapAt cells a b) a b = cells := by
  funext c
  dsimp [swapAt]
  grind

lemma tile_ne_zero_of_ne_blank {B : Board} {cells : Cell B → ℕ}
    (hv : IsValid B cells) {a b : Cell B} (ha0 : cells a = 0) (hne : a ≠ b) :
    cells b ≠ 0 := by
  intro h0
  exact hne (ExistsUnique.unique hv.2.1 h0 ha0).symm

lemma swapAt_valid {B : Board} {cells : Cell B → ℕ} (hv : IsValid B cells)
    (a b : Cell B) (ha0 : cells a = 0) (hne : a ≠ b) :
    IsValid B (swapAt cells a b) := by
  rcases hv with ⟨hle, ⟨b0, hb0, huniq0⟩, htiles⟩
  have hv' : IsValid B cells := ⟨hle, ⟨b0, hb0, huniq0⟩, htiles⟩
  have hbne0 := tile_ne_zero_of_ne_blank hv' ha0 hne
  constructor
  · exact swapAt_le hle a b
  constructor
  · refine ExistsUnique.intro b (swapAt_b ha0) ?_
    intro c hc0
    dsimp [swapAt] at hc0
    by_cases hca : c = a <;> by_cases hcb : c = b
    · exact absurd (hca.symm ▸ hcb) hne
    · simp [hca] at hc0
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
        simp [hib]
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
          simp [hja] at hj ⊢
          subst hja
          have hib : i = b := (huniq b hj).symm
          simp [hib]
      · by_cases hjb : j = b
        · have h0 : 0 = k := by
            rw [hjb, swapAt_b ha0] at hj
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
noncomputable def slide {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) : Config B :=
  { cells := swapAt cfg.cells (blank cfg) n
    valid := swapAt_valid cfg.valid (blank cfg) n (blank_zero cfg) (adjacent_ne h) }

lemma blank_slide {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) :
    blank (slide cfg n h) = n := by
  apply ExistsUnique.unique
    (swapAt_valid cfg.valid (blank cfg) n (blank_zero cfg) (adjacent_ne h)).2.1
    (blank_zero (slide cfg n h))
  dsimp [slide]
  exact swapAt_b (blank_zero cfg)

/-- `cfg'` is one legal move away from `cfg`. -/
def legalStep {B : Board} (cfg cfg' : Config B) : Prop :=
  ∃ n : Cell B, ∃ h : adjacent (blank cfg) n, cfg' = slide cfg n h

/-- Reachability via legal moves. -/
def Reachable {B : Board} : Config B → Config B → Prop :=
  Relation.ReflTransGen legalStep

/-- Standard goal labels: row-major tiles, blank at bottom-right. -/
def goalCells (B : Board) (c : Cell B) : ℕ :=
  if c = bottomRight B then 0 else rankExcept (bottomRight B) c + 1

lemma goalCells_le (B : Board) (c : Cell B) : goalCells B c ≤ B.tileCount := by
  rw [goalCells]
  by_cases hc : c = bottomRight B
  · simp [hc]
  · simp [hc]
    have hlt := rankExcept_lt (skip := bottomRight B) (c := c) hc
    rw [cellsRowMajorExcept_length] at hlt
    omega

lemma goalCells_eq_zero (B : Board) (c : Cell B) :
    goalCells B c = 0 ↔ c = bottomRight B := by
  constructor
  · intro hzero
    by_cases hc : c = bottomRight B
    · exact hc
    · rw [goalCells] at hzero
      simp [hc] at hzero
  · intro hc
    rw [goalCells]
    simp [hc]

lemma goal_ex_unique_blank (B : Board) : ∃! b : Cell B, goalCells B b = 0 := by
  refine ⟨bottomRight B, by simp [goalCells], ?_⟩
  intro b hb
  exact (goalCells_eq_zero B b).mp hb

lemma goal_ex_unique_labels (B : Board) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ B.tileCount) :
    ∃! i : Cell B, goalCells B i = k := by
  let j := k - 1
  have hj : j < (cellsRowMajorExcept (bottomRight B)).length := by
    rw [cellsRowMajorExcept_length]
    omega
  let i := (cellsRowMajorExcept (bottomRight B))[j]'hj
  have himem : i ∈ cellsRowMajorExcept (bottomRight B) := List.getElem_mem hj
  have hine : i ≠ bottomRight B := cellsRowMajorExcept_ne himem
  have hirank : rankExcept (bottomRight B) i = j :=
    rankExcept_cellsRowMajorExcept (bottomRight B) j hj
  refine ExistsUnique.intro i ?_ ?_
  · rw [goalCells]
    simp [hine, hirank]
    omega
  · intro i' hi'
    have hi_ne : i' ≠ bottomRight B := by
      intro hbr
      rw [goalCells] at hi'
      simp [hbr] at hi'
      omega
    have hrank : rankExcept (bottomRight B) i' = j := by
      rw [goalCells] at hi'
      simp [hi_ne] at hi'
      omega
    exact rankExcept_injective hi_ne hine (hrank.trans hirank.symm)

/-- Package `goalCells` + proofs into `Config`. -/
def goal (B : Board) : Config B :=
  ⟨goalCells B,
    ⟨goalCells_le B,
      goal_ex_unique_blank B,
      fun _ hk => goal_ex_unique_labels B hk⟩⟩

lemma blank_goal (B : Board) : blank (goal B) = bottomRight B := by
  apply ExistsUnique.unique (goal B).valid.2.1
  · exact blank_zero (goal B)
  · change goalCells B (bottomRight B) = 0
    simp [goalCells]

/-- README-style tile list `L`: row-major labels, skipping the current blank. -/
noncomputable def tileList {B : Board} (cfg : Config B) : List ℕ :=
  (cellsRowMajorExcept (blank cfg)).map cfg.cells

lemma tileList_length {B : Board} (cfg : Config B) :
    (tileList cfg).length = B.tileCount := by
  rw [tileList, List.length_map, cellsRowMajorExcept_length]

lemma cfg_cells_injective_of_ne_blank {B : Board} (cfg : Config B) {i j : Cell B}
    (hi : i ≠ blank cfg) (hij : cfg.cells i = cfg.cells j) :
    i = j := by
  have hi0 : cfg.cells i ≠ 0 := by
    intro h0
    exact hi (ExistsUnique.unique cfg.valid.2.1 h0 (blank_zero cfg))
  have hk : 1 ≤ cfg.cells i ∧ cfg.cells i ≤ B.tileCount := by
    constructor
    · omega
    · exact cfg.valid.1 i
  rcases cfg.valid.2.2 (cfg.cells i) hk with ⟨w, hw, huniq⟩
  have hji : j = i := (huniq j hij.symm).trans (huniq i rfl).symm
  exact hji.symm

lemma tileList_get_rankExcept {B : Board} (cfg : Config B) (c : Cell B)
    (hc : c ≠ blank cfg) :
    (tileList cfg)[rankExcept (blank cfg) c]'(by
      rw [tileList, List.length_map]
      exact rankExcept_lt hc) = cfg.cells c := by
  simp [tileList, List.getElem_map, rankExcept_getElem hc]

lemma tileList_nodup {B : Board} (cfg : Config B) : (tileList cfg).Nodup := by
  rw [tileList]
  refine List.Nodup.map_on ?_ (cellsRowMajorExcept_nodup _)
  intro a ha b hb hab
  exact cfg_cells_injective_of_ne_blank cfg
    (cellsRowMajorExcept_ne ha) hab

end NPuzzle.Rect
