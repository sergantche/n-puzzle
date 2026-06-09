import NPuzzle.Rect.TileInverse
import NPuzzle.Rect.TileRelabel

namespace NPuzzle.Rect

/-!
Abstract realized tile permutations for a rectangular board.

Concrete geometry only needs to prove that certain generator permutations are
realized by reachable configurations.  This file packages the reusable algebra:
realized permutations form a subgroup, and closures of realized generators are
realized.
-/

/-- A permutation of tiles is realized by a reachable configuration with blank at `bottomRight`. -/
def PermRealizable {B : Board} (σ : Equiv.Perm (Fin B.tileCount)) : Prop :=
  ∃ (cfg : Config B) (hbr : blank cfg = bottomRight B),
    Reachable (goal B) cfg ∧ permOfCfg cfg hbr = σ

lemma permRealizable_one (B : Board) :
    PermRealizable (B := B) 1 :=
  ⟨goal B, blank_goal B, Relation.ReflTransGen.refl, permOfCfg_goal B⟩

lemma relabelConfig_goal_eq_of_perm {B : Board} {σ : Equiv.Perm (Fin B.tileCount)}
    {cfg : Config B} (hbr : blank cfg = bottomRight B) (hperm : permOfCfg cfg hbr = σ) :
    relabelConfig σ (goal B) = cfg := by
  apply config_eq_of_tileList_and_blank
  · rw [blank_relabelConfig, blank_goal, hbr]
  · apply tileList_eq_of_tileListPerm_eq
      (tileList (relabelConfig σ (goal B))) (tileList cfg)
      (tileListSpec_of_config (relabelConfig σ (goal B)) (bottomRight B) (by
        rw [blank_relabelConfig σ (goal B)]
        exact blank_goal B))
      (tileListSpec_of_config cfg (bottomRight B) hbr)
    have hbrGoalRelabel : blank (relabelConfig σ (goal B)) = bottomRight B := by
      rw [blank_relabelConfig σ (goal B)]
      exact blank_goal B
    have hgoalperm : permOfCfg (relabelConfig σ (goal B)) hbrGoalRelabel = σ := by
      have h := permOfCfg_relabel σ (goal B) (blank_goal B)
      simpa [hbrGoalRelabel, permOfCfg_goal B] using h
    have hsame : permOfCfg (relabelConfig σ (goal B)) hbrGoalRelabel = permOfCfg cfg hbr := by
      rw [hgoalperm, hperm]
    simpa [permOfCfg] using hsame

lemma relabelConfig_perm_eq_goal {B : Board} {σ : Equiv.Perm (Fin B.tileCount)}
    {cfg : Config B} (hbr : blank cfg = bottomRight B) (hperm : permOfCfg cfg hbr = σ) :
    relabelConfig σ⁻¹ cfg = goal B := by
  apply config_eq_of_tileList_and_blank
  · rw [blank_relabelConfig, hbr, blank_goal]
  · apply tileList_eq_of_tileListPerm_eq
      (tileList (relabelConfig σ⁻¹ cfg)) (tileList (goal B))
      (tileListSpec_of_config (relabelConfig σ⁻¹ cfg) (bottomRight B) (by
        rw [blank_relabelConfig σ⁻¹ cfg]
        exact hbr))
      (tileListSpec_of_config (goal B) (bottomRight B) (blank_goal B))
    have hbrRelabel : blank (relabelConfig σ⁻¹ cfg) = bottomRight B := by
      rw [blank_relabelConfig σ⁻¹ cfg]
      exact hbr
    have hrel : permOfCfg (relabelConfig σ⁻¹ cfg) hbrRelabel = 1 := by
      have h := permOfCfg_relabel σ⁻¹ cfg hbr
      simpa [hbrRelabel, hperm] using h
    have hsame : permOfCfg (relabelConfig σ⁻¹ cfg) hbrRelabel =
        permOfCfg (goal B) (blank_goal B) := by
      rw [hrel, permOfCfg_goal B]
    simpa [permOfCfg] using hsame

lemma permRealizable_mul {B : Board} {σ τ : Equiv.Perm (Fin B.tileCount)}
    (hσ : PermRealizable (B := B) σ) (hτ : PermRealizable (B := B) τ) :
    PermRealizable (B := B) (σ * τ) := by
  obtain ⟨cfgσ, hbrσ, hreachσ, hpermσ⟩ := hσ
  obtain ⟨cfgτ, hbrτ, hreachτ, hpermτ⟩ := hτ
  refine ⟨relabelConfig σ cfgτ, by rw [blank_relabelConfig σ cfgτ]; exact hbrτ, ?_, ?_⟩
  · have hstart : relabelConfig σ (goal B) = cfgσ :=
      relabelConfig_goal_eq_of_perm hbrσ hpermσ
    have hreach_start : Reachable (goal B) (relabelConfig σ (goal B)) := by
      rwa [hstart]
    exact Relation.ReflTransGen.trans hreach_start (reachable_relabel σ hreachτ)
  · have h := permOfCfg_relabel σ cfgτ hbrτ
    simpa [hpermτ] using h

lemma permRealizable_inv {B : Board} {σ : Equiv.Perm (Fin B.tileCount)}
    (hσ : PermRealizable (B := B) σ) :
    PermRealizable (B := B) σ⁻¹ := by
  obtain ⟨cfg, hbr, hreach, hperm⟩ := hσ
  refine ⟨relabelConfig σ⁻¹ (goal B), by
    rw [blank_relabelConfig σ⁻¹ (goal B)]
    exact blank_goal B, ?_, ?_⟩
  · have hgoal : relabelConfig σ⁻¹ cfg = goal B :=
      relabelConfig_perm_eq_goal hbr hperm
    have hrelReach : Reachable (relabelConfig σ⁻¹ (goal B)) (relabelConfig σ⁻¹ cfg) :=
      reachable_relabel σ⁻¹ hreach
    rw [hgoal] at hrelReach
    exact reachable_symm hrelReach
  · have h := permOfCfg_relabel σ⁻¹ (goal B) (blank_goal B)
    simpa [permOfCfg_goal B] using h

def permRealizableSubgroup (B : Board) : Subgroup (Equiv.Perm (Fin B.tileCount)) where
  carrier := {σ | PermRealizable (B := B) σ}
  one_mem' := permRealizable_one B
  mul_mem' := by
    intro σ τ hσ hτ
    exact permRealizable_mul hσ hτ
  inv_mem' := by
    intro σ hσ
    exact permRealizable_inv hσ

lemma closure_le_realizable {B : Board} {S : Set (Equiv.Perm (Fin B.tileCount))}
    (hS : ∀ σ ∈ S, PermRealizable (B := B) σ) :
    Subgroup.closure S ≤ permRealizableSubgroup B := by
  rw [Subgroup.closure_le]
  intro σ hσ
  exact hS σ hσ

lemma permRealizable_of_mem_closure {B : Board} {S : Set (Equiv.Perm (Fin B.tileCount))}
    (hS : ∀ σ ∈ S, PermRealizable (B := B) σ)
    {σ : Equiv.Perm (Fin B.tileCount)} (hσ : σ ∈ Subgroup.closure S) :
    PermRealizable (B := B) σ :=
  closure_le_realizable hS hσ

end NPuzzle.Rect
