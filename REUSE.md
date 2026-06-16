# Reusable Lean artifacts

What others can import from this repository, and which modules are green but still 4×4-specific.  
Strategic context: [GOAL.md](GOAL.md) · proof status: [PLAN.md](PLAN.md).

---

## Three reuse layers

### Layer A — Pure list combinatorics

**Modules:** `NPuzzle/List/Inversion.lean` (shared definition and list-move lemmas) and `NPuzzle/FourFour/Inversion.lean` (current 4×4 puzzle-glue store).

**Provides:**

- `inversionCount`, `headInv`, `bubbleRight`, `bubbleLeft` in `NPuzzle.List`
- adjacent swap toggles `inversionCount mod 2` (with `Nodup`)
- `eraseIdx` / `insertIdx`: parity flips by `Nat.dist p q`
- `inversionCount_eq_zero_iff_sorted`, `exists_adjacent_gt_of_inversionCount_pos`

**Depends on today:** the reusable list layer has no puzzle dependency; some 4×4 parity lemmas still duplicate/import older puzzle glue.

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

### Layer C0 — Rectangular board geometry

| Module | Key exports |
|--------|-------------|
| `NPuzzle/Rect/Basic.lean` | `Board`, `Board.tileCount_ge_three`, `Cell`, `index`, `bottomRight`, `adjacent`, `adjacent_right`, `adjacent_left`, `adjacent_down`, `adjacent_up`, `cellsRowMajor`, `cellsRowMajorExcept`, `rankExcept_of_index_lt`, `rankExcept_of_index_gt`, `nonblankCellEquivFin` |
| `NPuzzle/Rect/CellPerm.lean` | `permCongr_formPerm`, `nonblankSubtypeList`, `ofSubtype_swap`, `ofSubtype_formPerm_nonblankSubtypeList`, `nonblankPermOfCellPerm`, `tilePermOfCellPerm`, `tilePermOfCellPerm_irrel`, `tilePermOfCellPerm_congr_perm`, `ofSubtype_fix_bottomRight`, `tilePermOfCellPerm_ofSubtype_formPerm` |
| `NPuzzle/Rect/Config.lean` | `IsValid`, `Config`, `blank`, `slide`, `legalStep`, `Reachable`, `goal`, `tileList` |
| `NPuzzle/Rect/TileInverse.lean` | `slide_inv`, `legalStep_symm`, `reachable_symm` |
| `NPuzzle/Rect/Reach.lean` | `BlankGridPath`, `BlankGridPath.vertices`, `BlankGridPath.append`, `BlankGridPath.reverse`, `blankGridPath_row`, `blankGridPath_col`, `blankGridPath_any`, `followBlankGridPathStart`, `reachable_one_step`, `reachable_blank_gridPath`, `reachable_blank_any` |
| `NPuzzle/Rect/PathEffect.lean` | `listEndpoint`, `swapAlongList`, `cellPermAlongList`, `swapAlongList_append`, `cellPermAlongList_append`, `cellPermAlongList_eq_formPerm_cons`, `cellPermAlongList_closed_eq_formPerm`, `cellPermAlongList_closed_fix_start`, `swapAlongList_eq_cellPermAlongList`, `swapAlongList_of_not_mem`, `swapAlongBlankPathStart`, `swapAlongBlankPathStart_eq_swapAlongList`, `followBlankGridPathStart_cells` |
| `NPuzzle/Rect/PathList.lean` | `AdjacentChain`, `adjacentChain_iff_isChain`, `AdjacentChain_singleton`, `AdjacentChain_append`, `blankGridPathOfList`, `closedBlankGridPathOfList`, `vertices_blankGridPathOfList`, `vertices_closedBlankGridPathOfList` |
| `NPuzzle/Rect/PathTilePerm.lean` | `tilePermOfCellPerm_closed_list` |
| `NPuzzle/Rect/PathRealizable.lean` | `permOfCfg_eq_tilePermOfCellPerm_of_goal_cells`, `permOfCfg_followClosedPath_goal`, `closedPathPermRealizable` |
| `NPuzzle/Rect/PathSufficiency.lean` | `closedFullList_left_compat_of_prefix`, `formPerm_isCycle_of_nodup_toFinset_univ`, `support_formPerm_of_nodup_toFinset_univ`, `PrefixedFullRoute`, `reachable_goal_to_cfg_bottomRight_of_closedFullPath`, `tiles_to_goal_bottomRight_of_closedFullPath`, `reachable_goal_to_cfg_bottomRight_of_leftClosedFullPath`, `tiles_to_goal_bottomRight_of_leftClosedFullPath`, `reachable_goal_to_cfg_bottomRight_of_leftClosedFullList`, `tiles_to_goal_bottomRight_of_leftClosedFullList`, `reachable_goal_to_cfg_bottomRight_of_prefixedFullList`, `tiles_to_goal_bottomRight_of_prefixedFullList`, `reachable_goal_to_cfg_bottomRight_of_prefixedFullRoute`, `tiles_to_goal_bottomRight_of_prefixedFullRoute` |
| `NPuzzle/Rect/PathParity.lean` | `cellParity`, `cellParity_adjacent`, `AdjacentChain.cellParity_endpoint`, `AdjacentChain.length_even_of_endpoint`, `PrefixedFullRoute.length_eq_tileCount`, `PrefixedFullRoute.size_even`, `PrefixedFullRoute.size_mod_two_eq_zero`, `Board.size_mod_two_eq_one_of_odd_rows_odd_cols`, `PrefixedFullRoute.isEmpty_of_size_mod_two_eq_one`, `PrefixedFullRoute.isEmpty_of_odd_rows_odd_cols` |
| `NPuzzle/Rect/TwoColumnRoute.lean` | `colZero`, `colOneOfTwo`, `rowFromRowsMinusTwo`, `rowFromRowsMinusOne`, `twoColumnRouteYs`, `twoColumnRoute_nonblank`, two-column corner coordinate lemmas |
| `NPuzzle/Rect/Corner.lean` | `cornerLeft`, `cornerUp`, `cornerUpLeft`, `cornerLeftIdx`, `cornerUpLeftIdx`, `cornerUpIdx`, bottom-right 2x2 adjacency/distinctness lemmas, `cornerCyclePath`, `cornerCycleCells`, `cornerCycleCfg`, `blank_cornerCycleCfg`, `cornerCycleCfg_cells_*`, `reachable_cornerCycleCfg`, `reachable_cornerCycle_blank` |
| `NPuzzle/Rect/CornerPerm.lean` | `cornerPermList`, `cornerPerm`, `cornerPerm_apply_*`, `cornerPerm_apply_of_not_corner`, `cornerPerm_isThreeCycle` |
| `NPuzzle/Rect/CornerRealizable.lean` | `cornerCycleCfg_goal_eq_relabel_cornerPerm`, `permOfCfg_cornerCycleCfg_goal`, `cornerPerm_realizable` |
| `NPuzzle/Rect/FullCyclePerm.lean` | `fullCycleList`, `fullCyclePerm`, `fullCyclePerm_isCycle`, `fullCyclePerm_support_univ`, `fullCyclePerm_apply_cornerUpIdx` |
| `NPuzzle/Rect/Parity.lean` | `blankRowFromBottom`, `invStat`, `parityClass`, `targetParity` |
| `NPuzzle/Rect/Invariant.lean` | `tileList_slide_eq_erase_insert`, `invStat_slide_horizontal_mod`, `invStat_slide_vertical_mod`, `parityClass_legalStep`, `parityClass_reachable`, `reachable_imp_parity` |
| `NPuzzle/Rect/TileGlue.lean` | `config_eq_of_tileList_and_blank`, `reachable_goal_of_tileList`, `tileList_goal`, `cfg_eq_goal_of_tileList` |
| `NPuzzle/Rect/TilePerm.lean` | `TileListSpec`, `mem_Icc_of_nodup_len`, `cellsOfTileList`, `configOfTileList`, `tileList_configOfTileList`, `config_eq_configOfTileList`, `tileLabelAt`, `tileListPerm`, `permOfCfg`, `tileList_eq_of_permOfCfg_eq` |
| `NPuzzle/Rect/TileSorted.lean` | `eq_range_map_succ_of_sorted`, `tileList_eq_goalTileList_of_sorted`, `tileListPerm_sorted_eq_one` |
| `NPuzzle/Rect/TileSign.lean` | `adjSwap`, `tileListPerm_bubbleRight`, `sign_tileListPerm_eq_neg_one_pow`, `invStat_even_iff_perm_alternating` |
| `NPuzzle/Rect/TileRelabel.lean` | `relabelConfig`, `reachable_relabel`, `tileListPerm_relabel`, `tileListPerm_congr`, `permOfCfg_relabel` |
| `NPuzzle/Rect/Realizable.lean` | `PermRealizable`, `permRealizableSubgroup`, `permRealizable_mul`, `permRealizable_inv`, `permRealizable_of_mem_closure` |
| `NPuzzle/Rect/AbstractSufficiency.lean` | `invStat_even_of_parity_bottomRight`, `permRealizable_of_mem_alternating_of_generators`, `reachable_goal_to_cfg_bottomRight_of_parity_generators`, `tiles_to_goal_bottomRight_of_parity_generators` |
| `NPuzzle/Rect/GeneratorSufficiency.lean` | `reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle`, `tiles_to_goal_bottomRight_of_compatibleFullCycle`, `reachable_goal_to_cfg_bottomRight_of_cornerLeftFullCycle`, `tiles_to_goal_bottomRight_of_cornerLeftFullCycle`, `reachable_goal_to_cfg_bottomRight_of_fullCycle`, `tiles_to_goal_bottomRight_of_fullCycle` |

**Typical consumer:** the next `N×M` proof layer, after necessity/parity invariance and before rectangular generator macros/sufficiency.

**General:** parameterized by positive row/column counts; independent of 4×4 cell indices.

---

### Layer C — Blank geometry and config glue

| Module | Key exports |
|--------|-------------|
| `BlankGrid.lean`, `BlankReach.lean` | blank can reach any cell |
| `TileGlue.lean` | `tileList` + blank position determine `Config` |
| `TileSorted.lean` | sorted list + zero inversions ⇒ goal list |

**Typical consumer:** sufficiency proofs that first move the blank, then permute tiles.

---

### Layer D0 — Group-theoretic sufficiency tail

| Module | Key exports |
|--------|-------------|
| `NPuzzle/Group/CycleThree.lean` | `isPreprimitive_of_mem_full_cycle_and_three_cycle`, `alternatingGroup_le_of_mem_full_cycle_and_three_cycle` |

**Typical consumer:** a rectangular-grid proof after it has constructed two realizable tile permutations: a full cycle and a compatible 3-cycle.

**Geometry-free:** the module speaks only about subgroups of `Equiv.Perm α`, blocks, primitive actions, and `alternatingGroup`.

---

## Green but heavy / 4×4-specific

| Module | Reason |
|--------|--------|
| `TileReach.lean` | Closed proof of `permRealizable_of_mem_alternating`, but the current generators and block argument are tuned to `Fin 15` / 4×4. |
| `TileConnectivity.lean` | Closed 4×4 bottom-right connectivity, depends on the `TileReach` surface. |
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

-- Shared inversion-count definition:
import NPuzzle.List.Inversion

-- Closed 4×4 theorem:
import NPuzzle.FourFour.Sufficiency
#check NPuzzle.FourFour.solvability_four_four

-- Parameterized rectangular board geometry:
import NPuzzle.Rect.Basic

-- Parameterized rectangular configurations and moves:
import NPuzzle.Rect.Config

-- Parameterized rectangular parity statistic:
import NPuzzle.Rect.Parity

-- Rectangular parity invariance / necessity:
import NPuzzle.Rect.Invariant
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
| **R0** | Extract group tail: full cycle + compatible 3-cycle ⇒ `alternatingGroup` | done in `NPuzzle/Group/CycleThree.lean` |
| **R2** | Move `inversionCount` + namespace `Inversion` → `NPuzzle/List/Inversion.lean` (no `Cell`) | done for `inversionCount_erase_insert_mod` and list move helpers |
| **R3** | `FourFour/Inversion.lean` keeps only puzzle glue (`invStat_slide_vertical_mod`, …) | R2 |
| **R4** | Paper §5–6: table Lean name ↔ classical lemma (Calabro sign/taxicab, Conrad $A_{15}$) | paper draft |
| **R5** | **Mathlib PR** (project intention): generalized `inversionCount_erase_insert_mod` / list move helpers | after more cleanup and Mathlib review |
| **R6** | Add `NPuzzle.Rect.Basic` / `Config` / `Parity` / `Invariant` as the first board-generic layer | necessity/parity invariance, realizable corner 3-cycle, compatible full-cycle shape, closed-path-to-tile-cycle/sufficiency bridges, conditional named sufficiency, and the even-size obstruction for prefixed full routes done; full-cycle realization next |

**Intention:** upstream layer A to [mathlib4](https://github.com/leanprover-community/mathlib4) so any Mathlib project gets these lemmas via `import Mathlib.Data.List....`. Details and scope: [GOAL.md](GOAL.md#mathlib-contribution-intention). Puzzle modules (`tileList`, `permOfCfg`) stay in this repo.

---

## Paper mapping (planned)

| Classical idea | Lean anchor |
|----------------|-------------|
| $I(L)$ unchanged by horizontal slide | `invStat_slide_horizontal_mod` |
| Vertical slide = erase/insert in $L$ | `tileList_slide_eq_erase_insert` |
| $I(L) \bmod 2$ changes by board width | `invStat_slide_vertical_mod` |
| Necessity: reachable ⇒ parity class | `reachable_imp_parity` |
| $\mathrm{sign}(\sigma) = (-1)^{I(L)}$ | `sign_tileListPerm_eq_neg_one_pow` |
| Even tile perm ⇔ $A_{n-1}$ (blank fixed) | `invStat_even_iff_perm_alternating` |
| Sufficiency group tail: full cycle + 3-cycle contains alternating group | `alternatingGroup_le_of_mem_full_cycle_and_three_cycle` |
| 4×4 sufficiency: $A_{15}$ realized by slides | `permRealizable_of_mem_alternating` |

Full bibliography: [paper/literature.md](paper/literature.md).
