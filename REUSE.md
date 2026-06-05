# Reusable Lean artifacts

What others can import from this repository **without** closing the full 4×4 sufficiency proof.  
Strategic context: [GOAL.md](GOAL.md) · proof status: [PLAN.md](PLAN.md).

---

## Three reuse layers

### Layer A — Pure list combinatorics

**Module:** `NPuzzle/FourFour/Inversion.lean` (namespace `NPuzzle.FourFour.Inversion`, lines before the `FourFour`-specific glue).

**Provides:**

- `headInv`, `bubbleRight`, `bubbleLeft`
- adjacent swap toggles `inversionCount mod 2` (with `Nodup`)
- `eraseIdx` / `insertIdx`: parity flips by `Nat.dist p q`
- `inversionCount_eq_zero_iff_sorted`, `exists_adjacent_gt_of_inversionCount_pos`

**Depends on today:** `inversionCount` is defined in `FourFour.lean`; file also imports `TileListVertical` for puzzle lemmas at the bottom.

**Typical consumer:** any formalization where a move permutes a list and parity is the invariant (puzzles, sorting networks, permutation games).

---

### Layer B — Moves ↔ `tileList` ↔ permutation sign

| Module | Key exports |
|--------|-------------|
| `Invariant.lean` | `tileList_slide_horizontal` / vertical via imports; `parityClass_reachable`, `reachable_imp_parity` (**necessity**) |
| `TileListVertical.lean` | `tileList_slide_vertical` as `eraseIdx` / `insertIdx` |
| `TileSign.lean` | `sign_tileListPerm_eq_neg_one_pow`, `invStat_even_iff_perm_alternating` |
| `TilePerm.lean` | `TileListSpec`, `permOfCfg`, `configOfTileList`, `tileListPerm` |

**Typical consumer:** another board size or blank position, reusing the same encoding pattern (row-major list + rank index).

**4×4-specific today:** `Fin 16` cells, `bottomRight`, `Fin 15` tile indices.

---

### Layer C — Blank geometry and config glue

| Module | Key exports |
|--------|-------------|
| `BlankGrid.lean`, `BlankReach.lean` | blank can reach any cell |
| `TileGlue.lean` | `tileList` + blank position determine `Config` |
| `TileSorted.lean` | sorted list + zero inversions ⇒ goal list |

**Typical consumer:** sufficiency proofs that first move the blank, then permute tiles.

---

## Not reusable yet (do not re-export)

| Module | Reason |
|--------|--------|
| `TileReach.lean` | **1 `sorry`:** `permRealizable_of_mem_alternating` |
| `TileConnectivity.lean` | depends on `TileReach` |
| `TileMacros.lean` | corner 3-cycle macro tuned to 4×4 geometry |
| `Sufficiency.lean` | end-to-end theorem — integration test, not a library boundary |

---

## Quick import guide (today)

```lean
-- Necessity only (parity invariant under legal moves):
import NPuzzle.FourFour.Invariant

-- sign(tileListPerm) = (-1)^inversionCount at fixed blank:
import NPuzzle.FourFour.TileSign

-- List inversion lemmas (namespace Inversion):
import NPuzzle.FourFour.Inversion
```

Add to your `lakefile.toml`:

```toml
[[require]]
name = "n-puzzle"
git = "https://github.com/<owner>/n-puzzle.git"
```

(Replace `<owner>` when publishing; pin a commit hash for stability.)

---

## Extraction roadmap

Tracked in [PLAN.md](PLAN.md#reuse--extraction-roadmap). Summary:

| Step | Action | Blocks |
|------|--------|--------|
| **R1** | Keep this file aligned with green modules after each merge | — |
| **R2** | Move `inversionCount` + namespace `Inversion` → `NPuzzle/List/Inversion.lean` (no `Cell`) | 4×4 proof |
| **R3** | `FourFour/Inversion.lean` keeps only puzzle glue (`invStat_slide_vertical_mod`, …) | R2 |
| **R4** | Paper §5–6: table Lean name ↔ classical lemma (Calabro sign/taxicab, Conrad $A_{15}$) | paper draft |
| **R5** | **Mathlib PR** (project intention): generalized `inversionCount_erase_insert_mod` for `List α` | R2, then Mathlib review |

**Intention:** upstream layer A to [mathlib4](https://github.com/leanprover-community/mathlib4) so any Mathlib project gets these lemmas via `import Mathlib.Data.List....`. Details and scope: [GOAL.md](GOAL.md#mathlib-contribution-intention). Puzzle modules (`tileList`, `permOfCfg`) stay in this repo.

---

## Paper mapping (planned)

| Classical idea | Lean anchor |
|----------------|-------------|
| $I(L)$ unchanged by horizontal slide | `tileList_slide_horizontal` |
| Vertical slide = one adjacent transposition in $L$ | `tileList_slide_vertical` |
| $I(L) \bmod 2$ flips on vertical move | `invStat_slide_vertical_mod` |
| Necessity: reachable ⇒ parity class | `reachable_imp_parity` |
| $\mathrm{sign}(\sigma) = (-1)^{I(L)}$ | `sign_tileListPerm_eq_neg_one_pow` |
| Even tile perm ⇔ $A_{n-1}$ (blank fixed) | `invStat_even_iff_perm_alternating` |
| Sufficiency: $A_{15}$ realized by slides | `permRealizable_of_mem_alternating` (**open**) |

Full bibliography: [paper/literature.md](paper/literature.md).
