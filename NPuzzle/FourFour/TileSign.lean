import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import NPuzzle.FourFour
import NPuzzle.FourFour.Inversion
import NPuzzle.FourFour.TilePerm
import NPuzzle.FourFour.TileSorted

set_option maxHeartbeats 1600000

namespace NPuzzle.FourFour

open Inversion List Equiv Equiv.Perm

/-- Adjacent transposition on list indices `p` and `p + 1`. -/
noncomputable def adjSwap (p : Fin 14) : Equiv.Perm (Fin 15) :=
  Equiv.swap (⟨p.1, by omega⟩ : Fin 15) (⟨p.1 + 1, by omega⟩ : Fin 15)

lemma adjSwap_isSwap (p : Fin 14) : (adjSwap p).IsSwap := by
  refine ⟨_, _, ?_, rfl⟩
  simp

lemma sign_adjSwap (p : Fin 14) : sign (adjSwap p) = -1 := by
  exact (adjSwap_isSwap p).sign_eq

private lemma tileListSpec_bubbleRight (L : List ℕ) (hs : TileListSpec bottomRight L) (p : ℕ)
    (hp : p + 1 < L.length) :
    TileListSpec bottomRight (bubbleRight L p hp) := by
  refine ⟨by simp [bubbleRight, hs.length_eq], ?_, ?_⟩
  · exact bubbleRight_nodup L p hp hs.nodup
  · intro x hx
    have hxL : x ∈ L := (bubbleRight_perm L p hp).mem_iff.mp hx
    exact hs.mem_Icc x hxL

lemma inversionCount_bubbleRight_succ_of_gt (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hgt : L[p]'(Nat.lt_of_succ_lt hp) > L[p + 1]'hp) (_hnd : L.Nodup) :
    inversionCount (bubbleRight L p hp) + 1 = inversionCount L :=
  inversionCount_bubbleRight_succ L p hp hgt

lemma tileListPerm_bubbleRight (L : List ℕ) (hs : TileListSpec bottomRight L) (p : Fin 14)
    (hp : p.1 + 1 < L.length) :
    tileListPerm (bubbleRight L p.1 hp) (tileListSpec_bubbleRight L hs p.1 hp) =
      tileListPerm L hs * adjSwap p := by
  ext i
  fin_cases p
  all_goals
    fin_cases i
    all_goals
      simp [tileListPerm_apply, tileLabelAt, adjSwap, Equiv.swap_apply_left, Equiv.swap_apply_right,
        bubbleRight]
      <;> try rfl

lemma tileList_eq_goalTileList_of_sorted (L : List ℕ) (hs : TileListSpec bottomRight L)
    (hsorted : List.Pairwise (· ≤ ·) L) : L = (List.range 15).map (· + 1) :=
  eq_range15_map_succ_of_sorted L hs.length_eq hs.nodup hsorted hs.mem_Icc

lemma tileListPerm_sorted_eq_one (L : List ℕ) (hs : TileListSpec bottomRight L)
    (hsorted : List.Pairwise (· ≤ ·) L) :
    tileListPerm L hs = 1 := by
  ext i
  rw [tileListPerm_apply, tileLabelAt]
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have heq := tileList_eq_goalTileList_of_sorted L hs hsorted
  have hval : L[i]'hi = i.1 + 1 := by
    simp [heq]
  simp [hval]

lemma sign_tileListPerm_eq_neg_one_pow (L : List ℕ) (hs : TileListSpec bottomRight L) :
    sign (tileListPerm L hs) = (inversionCount L : ℤ).negOnePow := by
  induction h : inversionCount L generalizing L with
  | zero =>
    rw [tileListPerm_sorted_eq_one L hs ((inversionCount_eq_zero_iff_sorted L).mp h)]
    simp [Equiv.Perm.sign_one, Int.negOnePow_zero]
  | succ n ih =>
    have hpos : 0 < inversionCount L := by rw [h]; exact Nat.succ_pos n
    obtain ⟨p, ⟨hp1, hgt⟩⟩ := exists_adjacent_gt_of_inversionCount_pos L hpos
    have hs' := tileListSpec_bubbleRight L hs p hp1
    have hcount := inversionCount_bubbleRight_succ_of_gt L p hp1 hgt hs.nodup
    have hn' : inversionCount (bubbleRight L p hp1) = n := by linarith [hcount, h]
    have ih' := ih (bubbleRight L p hp1) hs' hn'
    have hlen : L.length = 15 := hs.length_eq
    have hp15 : p + 1 < 15 := by rwa [hlen] at hp1
    have hperm :=
      tileListPerm_bubbleRight L hs ⟨p, Nat.lt_succ_iff.mp hp15⟩ hp1
    have hsign : sign (tileListPerm L hs) = -((↑n : ℤ)).negOnePow := by
      have hgoal := ih'
      rw [hperm, Equiv.Perm.sign_mul, sign_adjSwap] at hgoal
      simpa [mul_neg, mul_one] using congrArg Neg.neg hgoal
    have hsucc : ((↑(n + 1) : ℤ)).negOnePow = -((↑n : ℤ)).negOnePow := by
      simpa [Nat.cast_add] using Int.negOnePow_succ (↑n : ℤ)
    exact hsign.trans hsucc.symm

lemma invStat_even_iff_perm_alternating (cfg : Config) (hbr : blank cfg = bottomRight) :
    invStat cfg % 2 = 0 ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin 15) := by
  have hspec := tileListSpec_of_config cfg bottomRight hbr
  unfold invStat
  simp [permOfCfg, mem_alternatingGroup, sign_tileListPerm_eq_neg_one_pow (tileList cfg) hspec,
    Int.negOnePow_eq_one_iff, Nat.even_iff]

lemma even_invStat_iff_perm_alternating (cfg : Config) (hbr : blank cfg = bottomRight) :
    Even (invStat cfg) ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin 15) := by
  rw [Nat.even_iff]
  exact invStat_even_iff_perm_alternating cfg hbr

end NPuzzle.FourFour
