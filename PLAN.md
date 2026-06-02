# Formalization plan (n-puzzle)

Repository goal: the [solvability criterion](README.md#target-theorem-solvability-criterion) in Lean 4.  
**Current focus:** the **4×4** special case (`NPuzzle.FourFour`).

---

## Target theorem (4×4)

```lean
theorem solvability_four_four (cfg : Config) :
    Reachable cfg goal ↔ parityClass cfg = parityClass goal
```

Matches the README for even `M = 4`:  
`I(L) + r_B ≡ 1 (mod 2)` ⟺ reachability of `goal`.

---

## Proof plan (steps 1–9)

| Step | Content | Module | Status |
|------|---------|--------|--------|
| **1** | Grid encoding, `Config`, `goal`, `tileList`, `invStat`, `blankRowFromBottom`, `parityClass`, `legalStep`, `Reachable` | `NPuzzle/FourFour.lean` | ✅ |
| **2** | Horizontal move preserves row-major list `L` | `Invariant.lean` (`tileList_swap_horizontal`, …) | ✅ |
| **3** | Vertical move: `L` as `eraseIdx` / `insertIdx` (ranks in `cellsRowMajorExcept`) | `TileListVertical.lean` | ✅ |
| **4** | Inversion parity: index shift by 1 toggles `inversionCount mod 2` (with `Nodup`) | `Inversion.lean` | ✅ |
| **5** | Vertical move flips `invStat mod 2`; horizontal does not; same for `parityClass` | `Inversion.lean` + `Invariant.lean` | ✅ |
| **6** | `parityClass` invariant under `legalStep` / `Reachable` | `Invariant.lean` (`parityClass_reachable`) | ✅ |
| **7** | At `goal`: `parityClass goal = 1` | `Invariant.lean` (`parityClass_goal`) | ✅ |
| **8** | **Necessity:** `Reachable cfg goal → parityClass cfg = 1` | `Invariant.lean` (`reachable_imp_parity`) | ✅ |
| **9** | **Sufficiency:** `parityClass cfg = 1 → Reachable cfg goal` | `TileCycles.lean` (`parity_imp_reachable`) | ❌ blocked on **9b.3** |

**Theorem status:** `solvability_four_four` is **proved modulo** `tiles_to_goal_at_bottomRight` (one `sorry` on the critical path).

---

## Step 9 — remaining work

| Substep | Content | Module | Status |
|---------|---------|--------|--------|
| **9a** | Blank grid connected; blank reachable in any `Config` | `BlankGrid.lean`, `BlankReach.lean` | ✅ |
| **9b.1** | Blank → `bottomRight` | `TileCycles.lean` (`reachable_blank_bottomRight`) | ✅ |
| **9b.2** | `tileList` + blank determine `cfg` | `TileGlue.lean` | ✅ |
| **9b.2a** | `invStat = 0` ⇒ sorted `tileList` = goal list | `TileSorted.lean`, `Inversion.lean` | ✅ |
| **9b.2b** | `invStat = 0` + blank at BR ⇒ `cfg = goal` | `TileGlue.lean` (`cfg_eq_goal_of_invStat_zero`) | ✅ |
| **9b.3** | Tile connectivity at `bottomRight` (even `invStat`) | `TileReach.lean`, `TilePerm.lean`, `TileSign.lean`, `TileConnectivity.lean` | ❌ **1 sorry** + `TileSign` build |
| **9b.gen** | Corner 3-cycle slide macro from `goal` | `TileMacros.lean` (`reachable_cornerRot_from_goal`) | ✅ |
| **9b.inv** | Slide inverse / `Reachable` symmetry | `TileInverse.lean` (new) | ✅ |
| **9c** | Assemble `parity_imp_reachable` | `TileCycles.lean` | ✅ (modulo 9b.3) |

### 9b.3 — what is left (mathematics)

With blank fixed at `bottomRight`, legal moves permute `tileList` (horizontal: identity on `L`; vertical: adjacent transposition in `L`).

To finish:

1. **`permRealizable_of_mem_alternating`** (`TileReach.lean`, **1 sorry**): every `σ ∈ alternatingGroup (Fin 15)` is realized by some `cfg` with blank at BR and `Reachable goal cfg`.

2. **`TileSign.lean`**: `invStat_even_iff_perm_alternating` and `sign (tileListPerm) = negOnePow (inversionCount)` (file must compile).

3. **`reachable_goal_to_cfg_bottomRight`** (`TileReach.lean`): proved modulo (1)–(2); uses `permOfCfg` + `configOfTileList`.

**Already in `TileConnectivity.lean`:** `tiles_to_goal_at_bottomRight` (via `reachable_symm` and `reachable_goal_to_cfg_bottomRight`); base case `invStat = 0`; symmetry via `TileInverse`.

Typical generators for (1): corner 3-cycle (`TileMacros`) + Mathlib `closure_three_cycles_eq_alternating`, or induction on `inversionCount` with `bubbleRight` tied to vertical slides.

---

## Sorry check

```text
NPuzzle/FourFour/TileReach.lean  — 1 sorry
  permRealizable_of_mem_alternating    (realize every σ ∈ A₁₅ from goal)
invStat_even_iff_perm_alternating — in TileSign.lean (build must be green).
reachable_goal_to_cfg_bottomRight — in TileReach.lean (modulo permRealizable).
```

Run: `rg 'sorry' NPuzzle/`

---

## Module map (4×4)

| Module | Role |
|--------|------|
| `FourFour.lean` | Definitions |
| `Invariant.lean`, `Inversion.lean`, `TileListVertical.lean` | Steps 2–5 |
| `BlankGrid.lean`, `BlankReach.lean` | 9a |
| `TileGlue.lean`, `TileSorted.lean` | 9b.2, glue |
| `TileMacros.lean` | Generators (`cornerRotCells` reference) |
| `TileRank.lean` | `rankExcept` at `bottomRight` |
| `TileInverse.lean` | `slide_inv`, `reachable_symm` |
| `TilePerm.lean` | 9b.3 perm bridge (`tileListPerm`, `permOfCfg`, `configOfTileList`) |
| `TileSign.lean` | sign / parity ↔ `alternatingGroup` |
| `TileReach.lean` | `PermRealizable`, `reachable_goal_to_cfg_bottomRight` (**1 sorry**) |
| `TileConnectivity.lean` | 9b.3 assembly (`tiles_to_goal_at_bottomRight`) |
| `TileCycles.lean` | 9c |
| `Sufficiency.lean` | `solvability_four_four` |

---

## After 4×4 (out of scope for now)

- General `N×M` (separate theory / modules).
- Full README criterion for odd `M` (inversion-only).

---

## Quick links

- Main theorem: `NPuzzle/FourFour/Sufficiency.lean`
- Invariant chain: `NPuzzle/FourFour/Invariant.lean`
- Build: `lake build`
