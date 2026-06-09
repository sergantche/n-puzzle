import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace NPuzzle.List

open List

/-!
Basic inversion count for lists of natural-number labels.

Moving one list entry flips `inversionCount mod 2` according to the distance
between its old and new indices.  This is the geometry-free core used by both
the 4×4 proof and the rectangular proof.
-/

/-- Pair-inversion count for a list of natural numbers. -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if x > y then 1 else 0) 0 + inversionCount xs

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
  simp only [add_assoc]

lemma inversionCount_swap_zero (x y : ℕ) (xs : List ℕ) (hne : x ≠ y) :
    inversionCount (y :: x :: xs) % 2 = (inversionCount (x :: y :: xs) + 1) % 2 := by
  rw [inversionCount_two, inversionCount_two]
  have hgt : x > y ∨ y > x := Nat.lt_or_gt_of_ne hne.symm
  rcases hgt with hgt | hgt
  · simp [if_pos hgt, if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt))]
    omega
  · simp [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt)), if_pos hgt]
    omega

lemma inversionCount_swap_gt (x y : ℕ) (xs : List ℕ) (hgt : x > y) :
    inversionCount (y :: x :: xs) + 1 = inversionCount (x :: y :: xs) := by
  rw [inversionCount_two, inversionCount_two]
  simp only [if_pos hgt, if_neg (Nat.not_lt.mpr (Nat.le_of_lt hgt))]
  ring

lemma set_swap_succ (a : ℕ) (xs : List ℕ) (k : ℕ) (b c : ℕ)
    (hk : k + 2 < (a :: xs).length) :
    ((a :: xs).set (k + 1) b).set (k + 2) c =
      a :: ((xs.set k b).set (k + 1) c) := by
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
          ((x :: xs).set (k + 1) (x :: xs)[k + 1 + 1]).set
              (k + 1 + 1) (x :: xs)[k + 1] =
            x :: ((xs.set k xs[k + 1]).set (k + 1) xs[k]) := by
        simpa [Nat.add_assoc] using set_swap_succ x xs k xs[k + 1] xs[k] hk
      rw [hswap, inversionCount_def_cons,
        headInv_swap x xs k hi' (by simpa [List.getElem_cons_succ] using hne),
        inversionCount_def_cons]
      have hgt' : xs[k] > xs[k + 1] := by simpa [List.getElem_cons_succ] using hgt
      have h := ih k hi' (by simpa [List.getElem_cons_succ] using hne) hgt'
      omega

lemma inversionCount_swapAdjacent (L : List ℕ) (i : ℕ) (hi : i + 1 < L.length)
    (hne : L[i] ≠ L[i + 1]) :
    inversionCount (L.set i L[i + 1] |>.set (i + 1) L[i]) % 2 =
      (inversionCount L + 1) % 2 := by
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
          ((x :: xs).set (k + 1) (x :: xs)[k + 1 + 1]).set
              (k + 1 + 1) (x :: xs)[k + 1] =
            x :: ((xs.set k xs[k + 1]).set (k + 1) xs[k]) := by
        simpa [Nat.add_assoc] using set_swap_succ x xs k xs[k + 1] xs[k] hk
      rw [hswap, inversionCount_def_cons,
        headInv_swap x xs k hi' (by simpa [List.getElem_cons_succ] using hne),
        inversionCount_def_cons]
      have h := ih k hi' (by simpa [List.getElem_cons_succ] using hne)
      omega

lemma nodup_getElem_adjacent_ne {L : List ℕ} (hnd : L.Nodup) {p : ℕ}
    (hp : p + 1 < L.length) :
    L[p] ≠ L[p + 1] := by
  intro heq
  have := hnd.getElem_inj_iff.mp heq
  omega

lemma length_eraseIdx_insertIdx (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (hq : q < L.length) :
    ((L.eraseIdx p).insertIdx q (L[p]'hp)).length = L.length := by
  have hle : q ≤ (L.eraseIdx p).length := by rw [List.length_eraseIdx, if_pos hp]; omega
  rw [List.length_insertIdx_of_le_length hle, List.length_eraseIdx, if_pos hp]
  omega

/-- One step toward a larger index. -/
def bubbleRight (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) : List ℕ :=
  (L.set p (L[p + 1]'hp) |>.set (p + 1)
    (L[p]'(Nat.lt_of_le_of_lt (Nat.le_succ p) hp)))

def bubbleLeft (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (_hp1 : p - 1 < L.length) (_hp : p < L.length) : List ℕ :=
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

lemma eraseIdx_insertIdx_adjacent_perm (L : List ℕ) (p : ℕ)
    (hp : p < L.length) (hp' : p + 1 < L.length) :
    ((L.eraseIdx p).insertIdx (p + 1) (L[p]'hp)).Perm L := by
  induction p generalizing L with
  | zero =>
    cases L with
    | nil => simp at hp
    | cons x xs =>
      cases xs with
      | nil => simp at hp'
      | cons y zs =>
        simp [List.eraseIdx, List.insertIdx]
        exact List.Perm.swap x y zs
  | succ p ih =>
    cases L with
    | nil => simp at hp
    | cons a xs =>
      have hpxs : p < xs.length := by simp [List.length_cons] at hp; omega
      have hp'xs : p + 1 < xs.length := by simp [List.length_cons] at hp'; omega
      simp only [List.eraseIdx, List.getElem_cons_succ]
      rw [List.insertIdx_succ_cons]
      exact List.Perm.cons a (ih xs hpxs hp'xs)

lemma bubbleLeft_eq (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) :
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
        simp only [bubbleLeft, bubbleRight, List.eraseIdx, List.getElem_cons_succ,
          Nat.succ_sub_one]
        rw [List.insertIdx_succ_cons]
        exact congrArg _ (ih (p + 1) hp0' hp1' hp')

lemma bubbleLeft_eraseIdx (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (_hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleLeft L p hp0 _hp1 hp).eraseIdx (p - 1) = L.eraseIdx p := by
  rw [bubbleLeft_eq, List.eraseIdx_insertIdx_self]

lemma bubbleRight_get (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hp' : p < L.length) :
    (bubbleRight L p hp)[p + 1]'(by simp [bubbleRight, List.length_set]; exact hp) =
      L[p]'hp' := by
  simp only [bubbleRight, List.getElem_set]
  split_ifs <;> omega

lemma bubbleRight_get_at (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hp' : p < L.length) :
    (bubbleRight L p hp)[p]'(by simp [bubbleRight, List.length_set]; exact hp') =
      L[p + 1]'hp := by
  simp only [bubbleRight, List.getElem_set, if_neg (by omega : ¬p + 1 = p)]
  split_ifs <;> rfl

lemma bubbleRight_get_left (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleRight L (p - 1) (by omega))[p - 1]'(by
        simp [bubbleRight, List.length_set]
        exact hp1) =
      L[p]'hp := by
  simp only [bubbleRight, List.getElem_set, show p - 1 + 1 = p from by omega,
    if_neg (by omega : ¬p = p - 1)]
  split_ifs <;> rfl

lemma bubbleLeft_get (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleLeft L p hp0 hp1 hp)[p - 1]'(by
        simp [bubbleLeft, bubbleRight, List.length_set]
        exact hp1) =
      L[p]'hp := by
  simp only [bubbleLeft, bubbleRight_get_left L p hp0 hp1 hp]

lemma bubbleRight_eraseIdx (L : List ℕ) (p : ℕ)
    (_hp : p < L.length) (hp2 : p + 1 < L.length) :
    (bubbleRight L p hp2).eraseIdx (p + 1) = L.eraseIdx p := by
  rw [← swapAdjacent_eq_erase_insert, List.eraseIdx_insertIdx_self]

lemma bubbleRight_erase_insert (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (_hp1 : p + 1 < q)
    (_hq : q < L.length) (hp2 : p + 1 < L.length) :
    (L.eraseIdx p).insertIdx q (L[p]'hp) =
      ((bubbleRight L p hp2).eraseIdx (p + 1)).insertIdx q (L[p]'hp) := by
  rw [← bubbleRight_eraseIdx L p hp hp2]

lemma bubbleLeft_erase_insert (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (_hqp : q < p)
    (_hq : q < L.length) (hp0 : 0 < p) (hp1 : p - 1 < L.length) :
    (L.eraseIdx p).insertIdx q (L[p]'hp) =
      ((bubbleLeft L p hp0 hp1 hp).eraseIdx (p - 1)).insertIdx q (L[p]'hp) := by
  rw [← bubbleLeft_eraseIdx L p hp0 hp1 hp]

lemma inversionCount_bubbleRight_mod (L : List ℕ) (p : ℕ)
    (hp : p + 1 < L.length) (hnd : L.Nodup) :
    inversionCount (bubbleRight L p hp) % 2 = (inversionCount L + 1) % 2 := by
  dsimp [bubbleRight]
  exact inversionCount_swapAdjacent L p hp (nodup_getElem_adjacent_ne hnd hp)

lemma bubbleRight_perm (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length) :
    (bubbleRight L p hp).Perm L := by
  rw [← swapAdjacent_eq_erase_insert]
  exact eraseIdx_insertIdx_adjacent_perm L p (Nat.lt_of_succ_lt hp) hp

lemma bubbleLeft_perm (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) :
    (bubbleLeft L p hp0 hp1 hp).Perm L := by
  unfold bubbleLeft
  simpa using bubbleRight_perm L (p - 1) (by omega)

lemma bubbleRight_nodup (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hnd : L.Nodup) :
    (bubbleRight L p hp).Nodup :=
  List.Nodup.perm hnd (bubbleRight_perm L p hp).symm

lemma bubbleLeft_nodup (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) (hnd : L.Nodup) :
    (bubbleLeft L p hp0 hp1 hp).Nodup :=
  bubbleRight_nodup L (p - 1) (by omega) hnd

lemma inversionCount_bubbleLeft_mod (L : List ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp1 : p - 1 < L.length) (hp : p < L.length) (hnd : L.Nodup) :
    inversionCount (bubbleLeft L p hp0 hp1 hp) % 2 =
      (inversionCount L + 1) % 2 :=
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

lemma list_perm_erase_insert (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (hq : q < L.length) (hne : p ≠ q) :
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
        have hbridge :
            (((bubbleRight L p hp1).eraseIdx (p + 1)).insertIdx q L[p]).Perm
              (bubbleRight L p hp1) := by
          convert hperm using 2
          exact hget.symm
        exact List.Perm.trans hbridge (bubbleRight_perm L p hp1)
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
        have hbridge :
            (((bubbleLeft L p hp0 hp1 hp).eraseIdx (p - 1)).insertIdx q L[p]).Perm
              (bubbleLeft L p hp0 hp1 hp) := by
          convert hperm using 2
          exact hget.symm
        exact List.Perm.trans hbridge (bubbleLeft_perm L p hp0 hp1 hp)

lemma inversionCount_erase_insert_mod (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (hq : q < L.length) (hne : p ≠ q) (hnd : L.Nodup) :
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

lemma inversionCount_erase_insert_odd (L : List ℕ) (p q : ℕ)
    (hp : p < L.length) (hq : q < L.length) (hne : p ≠ q) (hnd : L.Nodup)
    (hodd : Nat.dist p q % 2 = 1) :
    inversionCount (L.eraseIdx p |>.insertIdx q (L[p]'hp)) % 2 =
      (inversionCount L + 1) % 2 := by
  rw [inversionCount_erase_insert_mod L p q hp hq hne hnd, Nat.add_mod, hodd]
  omega

lemma map_erase_eq_eraseIdx_idxOf {α β : Type} [BEq α] [LawfulBEq α]
    (f : α → β) (a : α) (xs : List α) :
    (xs.erase a).map f = (xs.map f).eraseIdx (xs.idxOf a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.idxOf_cons]
      by_cases hxa : x = a
      · subst hxa
        simp
      · have hbeq : (x == a) = false := by
          simp [hxa]
        simp [List.erase, hbeq, ih]

def swapValues {α β : Type} [DecidableEq α] (f : α → β) (a b c : α) : β :=
  if c = a then f b else if c = b then f a else f c

lemma map_swapValues_of_not_mem {α β : Type} [DecidableEq α]
    (f : α → β) {a b : α} {xs : List α}
    (ha : a ∉ xs) (hb : b ∉ xs) :
    xs.map (swapValues f a b) = xs.map f := by
  apply List.map_congr_left
  intro c hc
  have hca : c ≠ a := by
    intro h
    exact ha (h ▸ hc)
  have hcb : c ≠ b := by
    intro h
    exact hb (h ▸ hc)
  simp [swapValues, hca, hcb]

lemma map_swapValues_eq_erase_insert {α β : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] (f : α → β) (xs : List α) {a b : α}
    (hnd : xs.Nodup) (ha : a ∈ xs) (hb : b ∉ xs) (hne : a ≠ b) :
    xs.map (swapValues f a b) =
      ((xs.erase a).map f).insertIdx (xs.idxOf a) (f b) := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      simp at hnd
      rcases hnd with ⟨hxnot, hndxs⟩
      by_cases hxa : x = a
      · subst x
        have hanot : a ∉ xs := hxnot
        have hbnot : b ∉ xs := by
          intro h
          exact hb (List.mem_cons_of_mem a h)
        have hmap := map_swapValues_of_not_mem f (a := a) (b := b) hanot hbnot
        simp [List.erase, swapValues, hmap]
      · have haxs : a ∈ xs := by
          have hxa' : a ≠ x := fun h => hxa h.symm
          simpa [hxa'] using ha
        have hbnot : b ∉ xs := by
          intro h
          exact hb (List.mem_cons_of_mem x h)
        have hxb : x ≠ b := by
          intro h
          exact hb (by simp [h])
        have hih := ih hndxs haxs hbnot hne
        have hbeq_xa : (x == a) = false := by simp [hxa]
        simp [List.erase, swapValues, hxa, hxb, hbeq_xa, hih]

lemma map_erase_swap_eq_move {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (f : α → β) (xs : List α) {a b : α}
    (hnd : xs.Nodup) (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    (xs.erase b).map (swapValues f a b) =
      (((xs.erase a).map f).eraseIdx ((xs.erase a).idxOf b)).insertIdx
        ((xs.erase b).idxOf a) (f b) := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      simp at hnd
      rcases hnd with ⟨hxnot, hndxs⟩
      by_cases hxa : x = a
      · subst x
        have hbxs : b ∈ xs := by
          simp [hne.symm] at hb
          exact hb
        have hanot : a ∉ xs := hxnot
        have hbanot : b ≠ a := hne.symm
        have hbnot_after : b ∉ xs.erase b := by
          intro hmem
          have hmem' := (hndxs.mem_erase_iff).mp hmem
          exact hmem'.1 rfl
        have hanot_after : a ∉ xs.erase b := by
          intro hmem
          exact hanot ((hndxs.mem_erase_iff).mp hmem).2
        have hmap := map_swapValues_of_not_mem f (a := a) (b := b) hanot_after hbnot_after
        have herase := map_erase_eq_eraseIdx_idxOf f b xs
        have hbeq_ab : (a == b) = false := by simp [hne]
        simpa [List.erase, swapValues, hne, hbanot, hanot, hbxs, hbeq_ab,
          List.idxOf_cons] using congrArg (fun t => f b :: t) (hmap.trans herase)
      · by_cases hxb : x = b
        · subst x
          have haxs : a ∈ xs := by
            have hba : a ≠ b := hne
            simpa [hba] using ha
          have hbnot : b ∉ xs := hxnot
          have hab : a ≠ b := hne
          have hreplace := map_swapValues_eq_erase_insert f xs hndxs haxs hbnot hab
          have hbeq_ba : (b == a) = false := by simp [hne.symm]
          simpa [List.erase, swapValues, hne, hne.symm, hxa, hbnot, hbeq_ba,
            List.idxOf_cons] using hreplace
        · have haxs : a ∈ xs := by
            have hxa' : a ≠ x := fun h => hxa h.symm
            simpa [hxa'] using ha
          have hbxs : b ∈ xs := by
            have hxb' : b ≠ x := fun h => hxb h.symm
            simpa [hxb'] using hb
          have hih := ih hndxs haxs hbxs hne
          have hbeq_xa : (x == a) = false := by simp [hxa]
          have hbeq_xb : (x == b) = false := by simp [hxb]
          simpa [List.erase, swapValues, hxa, hxb, hbeq_xa, hbeq_xb,
            List.idxOf_cons] using congrArg (fun t => f x :: t) hih

end NPuzzle.List
