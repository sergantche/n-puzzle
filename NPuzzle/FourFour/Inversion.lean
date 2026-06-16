import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Dist
import NPuzzle.FourFour
import NPuzzle.FourFour.TileListVertical

set_option maxHeartbeats 800000

namespace NPuzzle.FourFour

namespace Inversion

open List

/-!
Moving one list entry flips `inversionCount mod 2` iff the index shift is odd.

Proof idea (the lecture proof): decompose `eraseIdx` + `insertIdx` into `Nat.dist p q` adjacent
swaps; each adjacent transposition toggles parity when values are distinct (`Nodup`).
-/

def headInv (x : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldl (fun acc y => acc + if x > y then 1 else 0) 0

lemma headInv_add (x : ℕ) (xs : List ℕ) (a : ℕ) :
    xs.foldl (fun acc y => acc + if x > y then 1 else 0) a = a + headInv x xs := by
  induction xs generalizing a with
  | nil => simp [headInv]
  | cons y xs ih =>
    dsimp [headInv, List.foldl_cons]
    rw [ih (a + if x > y then 1 else 0)]
    simp only [zero_add]
    rw [ih (if x > y then 1 else 0)]
    ring

lemma headInv_cons (x y : ℕ) (xs : List ℕ) :
    headInv x (y :: xs) = (if x > y then 1 else 0) + headInv x xs := by
  change List.foldl (fun acc z => acc + if x > z then 1 else 0) 0 (y :: xs) = _
  rw [List.foldl_cons, zero_add, headInv_add]

lemma inversionCount_def_cons (x : ℕ) (xs : List ℕ) :
    inversionCount (x :: xs) = headInv x xs + inversionCount xs := rfl

lemma inversionCount_two (x y : ℕ) (xs : List ℕ) :
    inversionCount (x :: y :: xs) =
      (if x > y then 1 else 0) + headInv x xs + headInv y xs + inversionCount xs := by
  rw [inversionCount_def_cons, headInv_cons, inversionCount_def_cons]
  simp only [add_assoc, add_left_comm, add_comm]

lemma inversionCount_swap_zero (x y : ℕ) (xs : List ℕ) (hne : x ≠ y) :
    inversionCount (y :: x :: xs) % 2 = (inversionCount (x :: y :: xs) + 1) % 2 := by
  rw [inversionCount_two, inversionCount_two]
  have hgt : x > y ∨ y > x := Nat.lt_or_gt_of_ne hne.symm
  rcases hgt with hgt | hgt
  · simp [if_pos hgt, if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt))]; omega
  · simp [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt)), if_pos hgt]; omega

lemma inversionCount_swap_gt (x y : ℕ) (xs : List ℕ) (hgt : x > y) :
    inversionCount (y :: x :: xs) + 1 = inversionCount (x :: y :: xs) := by
  rw [inversionCount_two, inversionCount_two]
  simp only [if_pos hgt, if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt))]
  ring

lemma set_swap_succ (a : ℕ) (xs : List ℕ) (k : ℕ) (b c : ℕ) (hk : k + 2 < (a :: xs).length) :
    ((a :: xs).set (k + 1) b).set (k + 2) c = a :: ((xs.set k b).set (k + 1) c) := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hk
    | cons x xs => simp [List.set]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons x xs => simp [List.set]

lemma headInv_swap (a : ℕ) (xs : List ℕ) (k : ℕ) (hk : k + 1 < xs.length)
    (_hne : xs[k] ≠ xs[k + 1]) :
    headInv a (xs.set k xs[k + 1] |>.set (k + 1) xs[k]) = headInv a xs := by
  induction xs generalizing a k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      cases xs with
      | nil => simp at hk
      | cons y zs =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set] at hk ⊢
        simp only [headInv_cons]
        ring
    | succ k =>
      have hk' : k + 1 < xs.length := by simp [List.length_cons] at hk; omega
      have hne' : xs[k] ≠ xs[k + 1] := by simpa [List.getElem_cons_succ] using _hne
      simp only [List.getElem_cons_succ, List.set, headInv_cons, ih a k hk' hne']

lemma inversionCount_swapAdjacent_succ (L : List ℕ) (i : ℕ) (hi : i + 1 < L.length)
    (hne : L[i] ≠ L[i + 1]) (hgt : L[i] > L[i + 1]) :
    inversionCount (L.set i L[i + 1] |>.set (i + 1) L[i]) + 1 = inversionCount L := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp at hi
      | cons y zs =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set]
        exact inversionCount_swap_gt x y zs hgt
    | succ k =>
      have hi' : k + 1 < xs.length := by simp [List.length_cons] at hi; omega
      have hk : k + 2 < (x :: xs).length := by simp [List.length_cons] at hi; omega
      have hswap :
          ((x :: xs).set (k + 1) (x :: xs)[k + 1 + 1]).set (k + 1 + 1) (x :: xs)[k + 1] =
            x :: ((xs.set k xs[k + 1]).set (k + 1) xs[k]) := by
        simp [Nat.add_assoc]
      rw [hswap, inversionCount_def_cons,
        headInv_swap x xs k hi' (by simpa [List.getElem_cons_succ] using hne),
        inversionCount_def_cons]
      have hgt' : xs[k] > xs[k + 1] := by simpa [List.getElem_cons_succ] using hgt
      have h := ih k hi' (by simpa [List.getElem_cons_succ] using hne) hgt'
      omega

lemma inversionCount_swapAdjacent (L : List ℕ) (i : ℕ) (hi : i + 1 < L.length)
    (hne : L[i] ≠ L[i + 1]) :
    inversionCount (L.set i L[i + 1] |>.set (i + 1) L[i]) % 2 = (inversionCount L + 1) % 2 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      cases xs with
      | nil => simp at hi
      | cons y zs =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set]
        exact inversionCount_swap_zero x y zs hne
    | succ k =>
      have hi' : k + 1 < xs.length := by simp [List.length_cons] at hi; omega
      have hk : k + 2 < (x :: xs).length := by simp [List.length_cons] at hi; omega
      have hswap :
          ((x :: xs).set (k + 1) (x :: xs)[k + 1 + 1]).set (k + 1 + 1) (x :: xs)[k + 1] =
            x :: ((xs.set k xs[k + 1]).set (k + 1) xs[k]) := by
        simp [Nat.add_assoc]
      rw [hswap, inversionCount_def_cons,
        headInv_swap x xs k hi' (by simpa [List.getElem_cons_succ] using hne),
        inversionCount_def_cons]
      have h := ih k hi' (by simpa [List.getElem_cons_succ] using hne)
      omega

lemma nodup_getElem_adjacent_ne {L : List ℕ} (hnd : L.Nodup) {p : ℕ} (hp : p + 1 < L.length) :
    L[p] ≠ L[p + 1] := by
  intro heq
  have := hnd.getElem_inj_iff.mp heq
  omega

lemma length_eraseIdx_insertIdx (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q < L.length) :
    ((L.eraseIdx p).insertIdx q (L[p]'hp)).length = L.length := by
  have hle : q ≤ (L.eraseIdx p).length := by rw [List.length_eraseIdx, if_pos hp]; omega
  rw [List.length_insertIdx_of_le_length hle, List.length_eraseIdx, if_pos hp]
  omega

/-- One step toward larger index. -/
def bubbleRight (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) : List ℕ :=
  (L.set p (L[p + 1]'hp) |>.set (p + 1) (L[p]'(Nat.lt_of_le_of_lt (Nat.le_succ p) hp)))

def bubbleLeft (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (_hp1 : p - 1 < L.length) (_hp : p < L.length) : List ℕ :=
  bubbleRight L (p - 1) (by omega)

lemma swapAdjacent_eq_erase_insert (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) :
    (L.eraseIdx p).insertIdx (p + 1) (L[p]'(Nat.lt_of_succ_lt hp)) =
      bubbleRight L p hp := by
  induction p generalizing L with
  | zero =>
    cases L with
    | nil => simp at hp
    | cons x xs =>
      cases xs with
      | nil => simp at hp
      | cons y zs => simp [bubbleRight, List.eraseIdx, List.insertIdx, List.set]
  | succ p ih =>
    cases L with
    | nil => simp at hp
    | cons a xs =>
      have hp' : p + 1 < xs.length := by simp [List.length_cons] at hp; omega
      have hget : (a :: xs)[p + 1] = xs[p] := by simp [List.getElem_cons_succ]
      simp only [List.eraseIdx, List.set, List.getElem_cons_succ, hget, bubbleRight]
      rw [List.insertIdx_succ_cons, ih xs hp']
      simp [bubbleRight]

lemma inversionCount_bubbleRight_succ (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hgt : L[p]'(Nat.lt_of_succ_lt hp) > L[p + 1]'hp) :
    inversionCount (bubbleRight L p hp) + 1 = inversionCount L := by
  dsimp [bubbleRight]
  have hne : L[p]'(Nat.lt_of_succ_lt hp) ≠ L[p + 1]'hp := by omega
  exact inversionCount_swapAdjacent_succ L p hp hne hgt

lemma eraseIdx_insertIdx_adjacent_perm (L : List ℕ) (p : ℕ) (hp : p < L.length) (hp' : p + 1 < L.length) :
    ((L.eraseIdx p).insertIdx (p + 1) (L[p]'hp)) ~ L := by
  induction p generalizing L with
  | zero =>
    cases L with
    | nil => simp at hp
    | cons x xs =>
      cases xs with
      | nil => simp at hp'
      | cons y zs =>
        simp [List.eraseIdx, List.insertIdx]
        exact Perm.swap x y zs
  | succ p ih =>
    cases L with
    | nil => simp at hp
    | cons a xs =>
      have hpxs : p < xs.length := by simp [List.length_cons] at hp; omega
      have hp'xs : p + 1 < xs.length := by simp [List.length_cons] at hp'; omega
      simp only [List.eraseIdx, List.getElem_cons_succ]
      rw [List.insertIdx_succ_cons]
      exact Perm.cons a (ih xs hpxs hp'xs)

lemma bubbleLeft_eq (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length) (hp : p < L.length) :
    bubbleLeft L p hp0 hp1 hp = (L.eraseIdx p).insertIdx (p - 1) (L[p]'hp) := by
  induction L generalizing p with
  | nil => simp at hp
  | cons a xs ih =>
    cases p with
    | zero => omega
    | succ p =>
      cases p with
      | zero =>
        cases xs with
        | nil => simp at hp
        | cons b zs => simp [bubbleLeft, bubbleRight, List.eraseIdx, List.insertIdx, List.set]
      | succ p =>
        have hp' : p + 1 < xs.length := by simp [List.length_cons] at hp; omega
        have hp0' : 0 < p + 1 := by omega
        have hp1' : p < xs.length := by simp [List.length_cons] at hp1 hp; omega
        simp only [bubbleLeft, bubbleRight, List.eraseIdx, List.getElem_cons_succ, Nat.succ_sub_one]
        rw [List.insertIdx_succ_cons]
        exact congrArg _ (ih (p + 1) hp0' hp1' hp')

lemma bubbleLeft_eraseIdx (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (_hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleLeft L p hp0 _hp1 hp).eraseIdx (p - 1) = L.eraseIdx p := by
  rw [bubbleLeft_eq, List.eraseIdx_insertIdx_self]

lemma bubbleRight_get (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) (hp' : p < L.length) :
    (bubbleRight L p hp)[p + 1]'(by simp [bubbleRight, List.length_set]; exact hp) = L[p]'hp' := by
  simp only [bubbleRight, List.getElem_set]
  split_ifs <;> omega

lemma bubbleRight_get_at (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) (hp' : p < L.length) :
    (bubbleRight L p hp)[p]'(by simp [bubbleRight, List.length_set]; exact hp') = L[p + 1]'hp := by
  simp only [bubbleRight, List.getElem_set, if_neg (by omega : ¬p + 1 = p)]
  split_ifs <;> rfl

lemma bubbleRight_get_left (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleRight L (p - 1) (by omega))[p - 1]'(by simp [bubbleRight, List.length_set]; exact hp1) = L[p]'hp := by
  simp only [bubbleRight, List.getElem_set, show p - 1 + 1 = p from by omega, if_neg (by omega : ¬p = p - 1)]
  split_ifs <;> rfl

lemma bubbleLeft_get (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleLeft L p hp0 hp1 hp)[p - 1]'(by simp [bubbleLeft, bubbleRight, List.length_set]; exact hp1) =
      L[p]'hp := by
  simp only [bubbleLeft, bubbleRight_get_left L p hp0 hp1 hp]

lemma bubbleRight_eraseIdx (L : List ℕ) (p : ℕ) (_hp : p < L.length) (hp2 : p + 1 < L.length) :
    (bubbleRight L p hp2).eraseIdx (p + 1) = L.eraseIdx p := by
  rw [← swapAdjacent_eq_erase_insert, List.eraseIdx_insertIdx_self]

lemma bubbleRight_erase_insert (L : List ℕ) (p q : ℕ) (hp : p < L.length) (_hp1 : p + 1 < q)
    (_hq : q < L.length) (hp2 : p + 1 < L.length) :
    (L.eraseIdx p).insertIdx q (L[p]'hp) =
      ((bubbleRight L p hp2).eraseIdx (p + 1)).insertIdx q (L[p]'hp) := by
  rw [← bubbleRight_eraseIdx L p hp hp2]

lemma bubbleLeft_erase_insert (L : List ℕ) (p q : ℕ) (hp : p < L.length) (_hqp : q < p)
    (_hq : q < L.length) (hp0 : 0 < p) (hp1 : p - 1 < L.length) :
    (L.eraseIdx p).insertIdx q (L[p]'hp) =
      ((bubbleLeft L p hp0 hp1 hp).eraseIdx (p - 1)).insertIdx q (L[p]'hp) := by
  rw [← bubbleLeft_eraseIdx L p hp0 hp1 hp]

lemma inversionCount_bubbleRight_mod (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) (hnd : L.Nodup) :
    inversionCount (bubbleRight L p hp) % 2 = (inversionCount L + 1) % 2 := by
  dsimp [bubbleRight]
  exact inversionCount_swapAdjacent L p hp (nodup_getElem_adjacent_ne hnd hp)

lemma bubbleRight_perm (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) :
    bubbleRight L p hp ~ L := by
  rw [← swapAdjacent_eq_erase_insert]
  exact eraseIdx_insertIdx_adjacent_perm L p (Nat.lt_of_succ_lt hp) hp

lemma bubbleLeft_perm (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length) (hp : p < L.length) :
    bubbleLeft L p hp0 hp1 hp ~ L := by
  unfold bubbleLeft
  simpa using bubbleRight_perm L (p - 1) (by omega)

lemma bubbleRight_nodup (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) (hnd : L.Nodup) :
    (bubbleRight L p hp).Nodup :=
  Nodup.perm hnd (bubbleRight_perm L p hp).symm

lemma bubbleLeft_nodup (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length) (hp : p < L.length)
    (hnd : L.Nodup) :
    (bubbleLeft L p hp0 hp1 hp).Nodup :=
  bubbleRight_nodup L (p - 1) (by omega) hnd

lemma inversionCount_bubbleLeft_mod (L : List ℕ) (p : ℕ) (hp0 : 0 < p) (hp1 : p - 1 < L.length)
    (hp : p < L.length) (hnd : L.Nodup) :
    inversionCount (bubbleLeft L p hp0 hp1 hp) % 2 = (inversionCount L + 1) % 2 :=
  inversionCount_bubbleRight_mod L (p - 1) (by omega) hnd

lemma dist_succ_of_lt {p q : ℕ} (hpq : p < q) :
    Nat.dist p q = Nat.dist (p + 1) q + 1 := by
  rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hpq),
    Nat.dist_eq_sub_of_le (Nat.succ_le_of_lt hpq)]
  omega

lemma dist_succ_of_gt {p q : ℕ} (hpq : q < p) :
    Nat.dist p q = Nat.dist (p - 1) q + 1 := by
  have hqle : q ≤ p - 1 := by omega
  rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hpq), Nat.dist_eq_sub_of_le_right hqle]
  omega

lemma list_perm_erase_insert (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q < L.length) (hne : p ≠ q) :
    (L.eraseIdx p |>.insertIdx q (L[p]'hp)).Perm L := by
  induction hdist : Nat.dist p q generalizing L p q with
  | zero => exact absurd (Nat.eq_of_dist_eq_zero hdist) hne
  | succ d ih =>
    rcases Nat.lt_or_gt_of_ne hne with hpq | hqp
    · have hp1 : p + 1 < L.length := by omega
      by_cases hadj : p + 1 = q
      · subst q
        rw [swapAdjacent_eq_erase_insert L p hp1]
        exact bubbleRight_perm L p hp1
      · have hp2 : p + 1 < q := by omega
        have hd : Nat.dist (p + 1) q = d := by
          rw [dist_succ_of_lt hpq] at hdist
          exact Nat.succ.inj hdist
        have hne' : p + 1 ≠ q := by omega
        have hget := bubbleRight_get L p hp1 hp
        have hperm := ih (bubbleRight L p hp1) (p + 1) q
          (by simp [bubbleRight, List.length_set]; exact hp1)
          (by simp [bubbleRight, List.length_set]; omega) hne' hd
        rw [bubbleRight_erase_insert L p q hp hp2 hq hp1]
        have hbridge : ((bubbleRight L p hp1).eraseIdx (p + 1)).insertIdx q L[p] ~
            bubbleRight L p hp1 := by
          convert hperm using 2
          exact hget.symm
        exact Perm.trans hbridge (bubbleRight_perm L p hp1)
    · have hp0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le q) hqp
      have hp1 : p - 1 < L.length := by omega
      by_cases hadj : p - 1 = q
      · subst q
        rw [← bubbleLeft_eq L p hp0 hp1 hp]
        exact bubbleLeft_perm L p hp0 hp1 hp
      · have hd : Nat.dist (p - 1) q = d := by
          rw [dist_succ_of_gt hqp] at hdist
          exact Nat.succ.inj hdist
        have hne' : p - 1 ≠ q := by omega
        have hget := bubbleLeft_get L p hp0 hp1 hp
        have hperm := ih (bubbleLeft L p hp0 hp1 hp) (p - 1) q
          (by simp [bubbleLeft, bubbleRight, List.length_set]; exact hp1)
          (by simp [bubbleLeft, bubbleRight, List.length_set]; omega) hne' hd
        rw [bubbleLeft_erase_insert L p q hp hqp hq hp0 hp1]
        have hbridge : ((bubbleLeft L p hp0 hp1 hp).eraseIdx (p - 1)).insertIdx q L[p] ~
            bubbleLeft L p hp0 hp1 hp := by
          convert hperm using 2
          exact hget.symm
        exact Perm.trans hbridge (bubbleLeft_perm L p hp0 hp1 hp)

lemma inversionCount_erase_insert_mod (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q < L.length)
    (hne : p ≠ q) (hnd : L.Nodup) :
    inversionCount (L.eraseIdx p |>.insertIdx q (L[p]'hp)) % 2 =
      (inversionCount L + Nat.dist p q) % 2 := by
  induction hdist : Nat.dist p q generalizing L p q with
  | zero =>
    exact absurd (Nat.eq_of_dist_eq_zero hdist) hne
  | succ d ih =>
    rcases Nat.lt_or_gt_of_ne hne with hpq | hqp
    · have hp1 : p + 1 < L.length := by omega
      by_cases hadj : p + 1 = q
      · subst q
        have hd0 : d = 0 := by
          have h1 : Nat.dist p (p + 1) = 1 := by
            rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_succ_self p))]
            omega
          rw [h1] at hdist
          omega
        subst d
        have hval :
            (L.eraseIdx p).insertIdx (p + 1) (L[p]'hp) =
              (L.eraseIdx p).insertIdx (p + 1) (L[p]'(Nat.lt_of_succ_lt hp1)) := rfl
        rw [hval, swapAdjacent_eq_erase_insert L p hp1]
        exact inversionCount_bubbleRight_mod L p hp1 hnd
      · have hp2 : p + 1 < q := by omega
        have hd : Nat.dist (p + 1) q = d := by
          rw [dist_succ_of_lt hpq] at hdist
          exact Nat.succ.inj hdist
        have hne' : p + 1 ≠ q := by omega
        have hnd' := bubbleRight_nodup L p hp1 hnd
        rw [bubbleRight_erase_insert L p q hp hp2 hq hp1]
        have hih := ih (bubbleRight L p hp1) (p + 1) q
          (by simp [bubbleRight, List.length_set]; exact hp1)
          (by simp [bubbleRight, List.length_set]; omega)
          hne' hnd' hd
        have hget := bubbleRight_get L p hp1 hp
        apply Eq.trans ((congrArg (fun L' => inversionCount L' % 2) (by
          apply congrArg (fun x => ((bubbleRight L p hp1).eraseIdx (p + 1)).insertIdx q x)
          exact hget.symm)).trans hih)
        have hbr := inversionCount_bubbleRight_mod L p hp1 hnd
        omega
    · have hp0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le q) hqp
      have hp1 : p - 1 < L.length := by omega
      by_cases hadj : p - 1 = q
      · subst q
        have hd0 : d = 0 := by
          have h1 : Nat.dist p (p - 1) = 1 := by
            rw [Nat.dist_eq_sub_of_le_right (by omega)]
            omega
          rw [h1] at hdist
          omega
        subst d
        rw [← bubbleLeft_eq L p hp0 hp1 hp]
        exact inversionCount_bubbleLeft_mod L p hp0 hp1 hp hnd
      · have hd : Nat.dist (p - 1) q = d := by
          rw [dist_succ_of_gt hqp] at hdist
          exact Nat.succ.inj hdist
        have hne' : p - 1 ≠ q := by omega
        have hnd' := bubbleLeft_nodup L p hp0 hp1 hp hnd
        rw [bubbleLeft_erase_insert L p q hp hqp hq hp0 hp1]
        have hih := ih (bubbleLeft L p hp0 hp1 hp) (p - 1) q
          (by simp [bubbleLeft, bubbleRight, List.length_set]; exact hp1)
          (by simp [bubbleLeft, bubbleRight, List.length_set]; omega)
          hne' hnd' hd
        have hget := bubbleLeft_get L p hp0 hp1 hp
        apply Eq.trans ((congrArg (fun L' => inversionCount L' % 2) (by
          apply congrArg (fun x => ((bubbleLeft L p hp0 hp1 hp).eraseIdx (p - 1)).insertIdx q x)
          exact hget.symm)).trans hih)
        have hbl := inversionCount_bubbleLeft_mod L p hp0 hp1 hp hnd
        omega

lemma inversionCount_erase_insert_odd (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q < L.length)
    (hne : p ≠ q) (hnd : L.Nodup) (hodd : Nat.dist p q % 2 = 1) :
    inversionCount (L.eraseIdx p |>.insertIdx q (L[p]'hp)) % 2 = (inversionCount L + 1) % 2 := by
  rw [inversionCount_erase_insert_mod L p q hp hq hne hnd, Nat.add_mod, hodd]
  omega

lemma headInv_eq_zero {x : ℕ} {xs : List ℕ} : headInv x xs = 0 ↔ ∀ y ∈ xs, x ≤ y := by
  induction xs with
  | nil => simp [headInv]
  | cons a ys ih =>
    rw [headInv_cons]
    constructor
    · intro h z hz
      rw [mem_cons] at hz
      rcases hz with rfl | hz
      · by_cases hxy : x > z
        · simp [hxy] at h
        · simpa using Nat.le_of_not_gt hxy
      · by_cases hxy : x > a
        · simp [hxy] at h
        · simp [hxy] at h
          exact ih.mp h z hz
    · intro hall
      have htail : headInv x ys = 0 :=
        ih.mpr fun z hz => hall z (mem_cons_of_mem _ hz)
      by_cases hxy : x > a
      · have := hall _ mem_cons_self
        omega
      · simp [hxy, htail]

lemma headInv_pos_iff {x : ℕ} {xs : List ℕ} :
    0 < headInv x xs ↔ ∃ y ∈ xs, x > y := by
  constructor
  · intro hpos
    by_contra hall
    push Not at hall
    have hzero : headInv x xs = 0 := (headInv_eq_zero).2 fun y hy => hall y hy
    omega
  · rintro ⟨y, hy, hxy⟩
    rw [Nat.pos_iff_ne_zero, ne_eq, headInv_eq_zero]
    intro hall
    exact Nat.not_le.mpr hxy (hall y hy)

private lemma headInv_pos_gt_head_of_sorted {x : ℕ} {xs : List ℕ} (hx : 0 < headInv x xs)
    (hsorted : List.Pairwise (· ≤ ·) xs) (hne : xs ≠ []) :
    ∃ hx0 : 0 < xs.length, x > xs[0]'hx0 := by
  have hx0 : 0 < xs.length := List.length_pos_iff_ne_nil.mpr hne
  refine ⟨hx0, ?_⟩
  by_contra hxle
  push Not at hxle
  obtain ⟨y, hy, hxy⟩ := headInv_pos_iff.mp hx
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hy
  have hmono := (List.sortedLE_iff_getElem_le_getElem_of_le).mp (Pairwise.sortedLE hsorted)
  have h0lej : xs[0]'hx0 ≤ xs[j]'hj := hmono (Nat.zero_le j)
  have hley : x ≤ y := Nat.le_trans hxle (Nat.le_trans h0lej (Nat.le_of_eq heq))
  exact absurd hley (Nat.not_le.mpr hxy)

lemma inversionCount_eq_zero_iff_sorted (L : List ℕ) :
    inversionCount L = 0 ↔ List.Pairwise (· ≤ ·) L := by
  induction L with
  | nil => simp [inversionCount]
  | cons x xs ih =>
    simp [inversionCount_def_cons, headInv_eq_zero, ih, List.pairwise_cons, Nat.add_eq_zero_iff]

lemma exists_adjacent_gt_of_inversionCount_pos (L : List ℕ) (hpos : 0 < inversionCount L) :
    ∃ p, ∃ hp1 : p + 1 < L.length, L[p]'(Nat.lt_of_succ_lt hp1) > L[p + 1]'hp1 := by
  induction L with
  | nil => simp [inversionCount] at hpos
  | cons x xs ih =>
    rw [inversionCount_def_cons] at hpos
    by_cases hxs : 0 < inversionCount xs
    · obtain ⟨p, hp1, hgt⟩ := ih hxs
      refine ⟨p + 1, by simp [List.length_cons]; omega, ?_⟩
      simpa [List.getElem_cons_succ] using hgt
    · have hxs0 : inversionCount xs = 0 := by omega
      have hx : 0 < headInv x xs := by
        simp only [hxs0, add_zero] at hpos
        exact hpos
      have hsorted : List.Pairwise (· ≤ ·) xs := (inversionCount_eq_zero_iff_sorted xs).mp hxs0
      have hne : xs ≠ [] := by
        rintro rfl
        simp [headInv] at hx
      obtain ⟨_, hxgt⟩ := headInv_pos_gt_head_of_sorted hx hsorted hne
      refine ⟨0, by simp [List.length_cons]; exact List.length_pos_iff_ne_nil.mpr hne, ?_⟩
      rw [List.getElem_cons_zero, List.getElem_cons_succ]
      exact hxgt

end Inversion

lemma cellsRowMajorExcept_ne (b c : Cell) (hc : c ∈ cellsRowMajorExcept b) : c ≠ b := by
  intro rfl
  simp [cellsRowMajorExcept, List.mem_filter, List.mem_finRange] at hc

lemma cellsRowMajorExcept_nodup (b : Cell) : (cellsRowMajorExcept b).Nodup := by
  fin_cases b <;> simp [cellsRowMajorExcept, List.finRange, List.filter, List.Nodup]

lemma cfg_cells_injective_of_ne_blank (cfg : Config) {i j : Cell}
    (hi : i ≠ blank cfg) (hij : cfg.cells i = cfg.cells j) : i = j := by
  by_contra hne
  rcases cfg.valid with ⟨_, huniq0, htiles⟩
  by_cases h0i : cfg.cells i = 0
  · exact hi (ExistsUnique.unique huniq0 h0i (blank_zero cfg))
  · have hk : 1 ≤ cfg.cells i ∧ cfg.cells i ≤ 15 := by
      constructor <;> [omega; exact cfg.valid.1 i]
    rcases htiles (cfg.cells i) hk with ⟨wi, _, huniq⟩
    have hji : j = i := (huniq j hij.symm).trans (huniq i rfl).symm
    exact hne hji.symm

lemma rankExcept_lt {skip c : Cell} (hc : c ≠ skip) :
    rankExcept skip c < (cellsRowMajorExcept skip).length := by
  rw [cellsRowMajorExcept_length]
  fin_cases skip <;> fin_cases c <;>
    simp [rankExcept, cellsRowMajorExcept, List.finRange, List.filter,
      List.findIdx, List.findIdx.go] at hc ⊢

lemma rankExcept_getElem {skip c : Cell} (hc : c ≠ skip) :
    (cellsRowMajorExcept skip)[rankExcept skip c]'(rankExcept_lt hc) = c := by
  fin_cases skip <;> fin_cases c <;>
    simp [rankExcept, cellsRowMajorExcept, List.finRange, List.filter,
      List.findIdx, List.findIdx.go] at hc ⊢

lemma rankExcept_injective {skip : Cell} {c c' : Cell} (hc : c ≠ skip) (hc' : c' ≠ skip)
    (h : rankExcept skip c = rankExcept skip c') : c = c' := by
  exact (rankExcept_getElem hc).symm.trans (by simpa [h] using rankExcept_getElem hc')

lemma tileList_get_rankExcept (cfg : Config) (c : Cell) (hc : c ≠ blank cfg) :
    (tileList cfg)[rankExcept (blank cfg) c]'(by
      unfold tileList; rw [List.length_map]; exact rankExcept_lt hc) = cfg.cells c := by
  simp [tileList, List.getElem_map, rankExcept_getElem hc]

lemma tileList_nodup (cfg : Config) : (tileList cfg).Nodup := by
  rw [tileList]
  refine List.Nodup.map_on ?_ (cellsRowMajorExcept_nodup _)
  intro a ha b hb hab
  exact cfg_cells_injective_of_ne_blank cfg
    (cellsRowMajorExcept_ne _ _ ha) hab

lemma invStat_slide_vertical_mod (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    invStat (slide cfg n h) % 2 = (invStat cfg + 1) % 2 := by
  unfold invStat
  rw [tileList_slide_vertical cfg n h hc]
  simp only
  have hnd := tileList_nodup cfg
  have hne : rankExcept (blank cfg) n ≠ rankExcept n (blank cfg) := by
    intro heq
    have := rankExcept_vertical_mod (blank cfg) n h hc
    rw [heq] at this
    omega
  have hodd : Nat.dist (rankExcept (blank cfg) n) (rankExcept n (blank cfg)) % 2 = 1 := by
    have hsum := rankExcept_vertical_mod (blank cfg) n h hc
    set p := rankExcept (blank cfg) n
    set q := rankExcept n (blank cfg)
    rcases Nat.le_total p q with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hle]
      omega
  have hlt := rankExcept_vertical_lt (blank cfg) n h hc
  have hp : rankExcept (blank cfg) n < (tileList cfg).length := by
    simp [tileList, cellsRowMajorExcept_length]; exact hlt.1
  have hq : rankExcept n (blank cfg) < (tileList cfg).length := by
    simp [tileList, cellsRowMajorExcept_length]; exact hlt.2
  have hget :
      (tileList cfg)[rankExcept (blank cfg) n]'hp = cfg.cells n :=
    tileList_get_rankExcept cfg n (adjacent.ne h.symm)
  convert Inversion.inversionCount_erase_insert_odd (tileList cfg)
    (rankExcept (blank cfg) n) (rankExcept n (blank cfg)) hp hq hne hnd hodd using 1
  rw [hget]

end NPuzzle.FourFour
