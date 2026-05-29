import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.BlankReach
import NPuzzle.FourFour.TileMacros
import NPuzzle.FourFour.TilePerm
import NPuzzle.FourFour.TileSign

set_option maxHeartbeats 1600000

namespace NPuzzle.FourFour

open Equiv.Perm Inversion List

/-- Sorted tile list with blank at `bottomRight`. -/
def goalTileList : List ℕ := (List.range 15).map (· + 1)

lemma goalTileList_eq : tileList goal = goalTileList :=
  tileList_goal

/-- List after the corner macro (`11↦12↦15↦11` on values at cells `10,11,14`). -/
def cornerTileList : List ℕ :=
  goalTileList.map fun x =>
    if x = 11 then 12 else if x = 12 then 15 else if x = 15 then 11 else x

lemma cornerTileList_length : cornerTileList.length = 15 := by
  simp [cornerTileList, goalTileList]

lemma cornerTileList_nodup : cornerTileList.Nodup := by
  native_decide

lemma cornerTileList_mem_Icc : ∀ x ∈ cornerTileList, 1 ≤ x ∧ x ≤ 15 := by
  intro x hx
  simp only [cornerTileList, goalTileList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split_ifs <;> omega

lemma tileListSpec_corner : TileListSpec bottomRight cornerTileList where
  length_eq := cornerTileList_length
  nodup := cornerTileList_nodup
  mem_Icc := cornerTileList_mem_Icc

/-- Corner macro from any configuration with blank at `bottomRight`. -/
noncomputable def cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) : Config :=
  let h14 : adjacent (blank cfg) cell14 := by rw [hbr]; exact adjacent_bottomRight_cell14
  let c1 := slide cfg cell14 h14
  let h10 : adjacent (blank c1) cell10 := by
    rw [blank_slide cfg cell14 h14]
    exact adjacent_cell14_cell10
  let c2 := slide c1 cell10 h10
  let h11 : adjacent (blank c2) cell11 := by
    rw [blank_slide c1 cell10 h10]
    exact adjacent_cell10_cell11
  let c3 := slide c2 cell11 h11
  let h15 : adjacent (blank c3) bottomRight := by
    rw [blank_slide c2 cell11 h11]
    exact adjacent_cell11_bottomRight
  slide c3 bottomRight h15

lemma blank_cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) :
    blank (cornerRotAt cfg hbr) = bottomRight := by
  simp [cornerRotAt, blank_slide]

lemma reachable_cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) :
    Reachable cfg (cornerRotAt cfg hbr) := by
  let h14 : adjacent (blank cfg) cell14 := by rw [hbr]; exact adjacent_bottomRight_cell14
  let c1 := slide cfg cell14 h14
  let h10 : adjacent (blank c1) cell10 := by
    rw [blank_slide cfg cell14 h14]
    exact adjacent_cell14_cell10
  let c2 := slide c1 cell10 h10
  let h11 : adjacent (blank c2) cell11 := by
    rw [blank_slide c1 cell10 h10]
    exact adjacent_cell10_cell11
  let c3 := slide c2 cell11 h11
  let h15 : adjacent (blank c3) bottomRight := by
    rw [blank_slide c2 cell11 h11]
    exact adjacent_cell11_bottomRight
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c3 bottomRight h15)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c2 cell11 h11)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c1 cell10 h10)
  exact reachable_one_step cfg cell14 h14

/-- A permutation of tiles is realized by a reachable configuration (blank at `bottomRight`). -/
def PermRealizable (σ : Equiv.Perm (Fin 15)) : Prop :=
  ∃ (cfg : Config) (hbr : blank cfg = bottomRight), Reachable goal cfg ∧ permOfCfg cfg hbr = σ

lemma permRealizable_one : PermRealizable 1 :=
  ⟨goal, blank_goal, Relation.ReflTransGen.refl, permOfCfg_goal⟩

/-- Every even permutation is realized from `goal` (classical 15-puzzle group). -/
lemma permRealizable_of_mem_alternating {σ : Equiv.Perm (Fin 15)}
    (hσ : σ ∈ alternatingGroup (Fin 15)) : PermRealizable σ := by
  sorry

/-- From `goal`, reach any even-parity configuration with blank at `bottomRight`. -/
lemma reachable_goal_to_cfg_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (heven : invStat cfg % 2 = 0) : Reachable goal cfg := by
  by_cases h0 : invStat cfg = 0
  · rw [cfg_eq_goal_of_invStat_zero cfg hbr h0]
    exact Relation.ReflTransGen.refl
  · have hσ := (invStat_even_iff_perm_alternating cfg hbr).mp heven
    obtain ⟨cfg', hbr', hreach, hperm⟩ := permRealizable_of_mem_alternating hσ
    have hcfg : cfg = cfg' := by
      apply config_eq_of_tileList_and_blank cfg cfg'
      · rw [hbr, hbr']
      · exact tileList_eq_of_tileListPerm_eq _ _
          (tileListSpec_of_config cfg bottomRight hbr)
          (tileListSpec_of_config cfg' bottomRight hbr')
          (by simpa [permOfCfg] using hperm.symm)
    rw [hcfg]
    exact hreach

end NPuzzle.FourFour
