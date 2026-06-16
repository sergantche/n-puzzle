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
| `NPuzzle/Rect/PathSufficiency.lean` | `closedFullList_left_compat_of_prefix`, `formPerm_isCycle_of_nodup_toFinset_univ`, `support_formPerm_of_nodup_toFinset_univ`, `formPerm_isCycle_of_nodup_toFinset_erase`, `support_formPerm_of_nodup_toFinset_erase`, `PrefixedFullRoute`, `reachable_goal_to_cfg_bottomRight_of_closedFullPath`, `tiles_to_goal_bottomRight_of_closedFullPath`, `reachable_goal_to_cfg_bottomRight_of_closedAlmostFullPath`, `tiles_to_goal_bottomRight_of_closedAlmostFullPath`, `reachable_goal_to_cfg_bottomRight_of_leftClosedFullPath`, `tiles_to_goal_bottomRight_of_leftClosedFullPath`, `reachable_goal_to_cfg_bottomRight_of_leftClosedFullList`, `tiles_to_goal_bottomRight_of_leftClosedFullList`, `reachable_goal_to_cfg_bottomRight_of_closedAlmostFullList`, `tiles_to_goal_bottomRight_of_closedAlmostFullList`, `reachable_goal_to_cfg_bottomRight_of_prefixedFullList`, `tiles_to_goal_bottomRight_of_prefixedFullList`, `reachable_goal_to_cfg_bottomRight_of_prefixedFullRoute`, `tiles_to_goal_bottomRight_of_prefixedFullRoute` |
| `NPuzzle/Rect/PathParity.lean` | `cellParity`, `cellParity_adjacent`, `AdjacentChain.cellParity_endpoint`, `AdjacentChain.length_even_of_endpoint`, `closedFullList_size_even`, `closedFullList_size_mod_two_eq_zero`, `no_closedFullList_of_size_mod_two_eq_one`, `no_closedFullList_of_odd_rows_odd_cols`, `PrefixedFullRoute.length_eq_tileCount`, `PrefixedFullRoute.size_even`, `PrefixedFullRoute.size_mod_two_eq_zero`, `Board.size_mod_two_eq_one_of_odd_rows_odd_cols`, `PrefixedFullRoute.isEmpty_of_size_mod_two_eq_one`, `PrefixedFullRoute.isEmpty_of_odd_rows_odd_cols` |
| `NPuzzle/Rect/TwoColumnRoute.lean` | `colZero`, `colOneOfTwo`, `rowFromRowsMinusTwo`, `rowFromRowsMinusOne`, `finList_toFinset_eq_univ_of_nodup_length`, `finRange_head_val_eq_zero`, `finRange_getLast_val_add_one`, `finRange_head?_eq_zero`, `finRange_getLast?_eq_last`, `isChain_finRange_val_succ`, `isChain_finRange_reverse_val_pred`, `isChain_twoColumn_leftTail`, `isChain_twoColumn_rightColumn`, `twoColumnLeftTail`, `twoColumnRightColumn`, `twoColumnRouteYs`, `twoColumnRoute_nonblank`, `twoColumnRoute_length`, `twoColumnRoute_nodup_cells`, `twoColumnRoute_nodup`, `twoColumnRoute_covers`, `twoColumnRoute_chain`, `twoColumnPrefixedFullRoute`, `reachable_goal_to_cfg_bottomRight_of_twoColumn`, `tiles_to_goal_bottomRight_of_twoColumn`, two-column route boundary/segment and corner coordinate lemmas |
| `NPuzzle/Rect/Thin.lean` | `rows_eq_one_of_lt_two`, `cols_eq_one_of_lt_two`, `tileList_slide_horizontal`, `tileList_slide_vertical_of_cols_eq_one`, `tileList_reachable_of_rows_eq_one`, `tileList_reachable_of_cols_eq_one`, `tileList_reachable_of_rows_lt_two`, `tileList_reachable_of_cols_lt_two`, thin-board goal obstruction lemmas |
| `NPuzzle/Rect/TwoRowRoute.lean` | `rowZero`, `rowOneOfTwo`, `colFromColsMinusOne`, `twoRowBottomTail`, `twoRowTopRow`, `twoRowRouteXs`, `twoRowRoute_chain`, `twoRowRoute_nonblank`, `twoRowRoute_length`, `twoRowRoute_nodup_cells`, `twoRowRoute_nodup`, `twoRowRoute_covers`, `twoRowRoute_compat`, `reachable_goal_to_cfg_bottomRight_of_twoRow`, `tiles_to_goal_bottomRight_of_twoRow`, two-row route endpoint/boundary/chain lemmas |
| `NPuzzle/Rect/EvenColumnRoute.lean` | `evenColsBottomTail`, `evenColsUpperColumn`, `evenColsUpperSnake`, `evenColsRouteXs`, `evenColsUpperColumn_length`, `evenColsUpperSnake_length`, `evenColsRoute_length`, `isChain_evenColsBottomTail`, `isChain_evenColsUpperColumn`, `isChain_evenColsUpperSnake`, `evenColsRoute_chain_open`, `evenColsRoute_chain`, `evenColsRoute_head`, `evenColsRoute_getLast`, `evenColsRoute_compat`, `reachable_goal_to_cfg_bottomRight_of_evenCols`, `tiles_to_goal_bottomRight_of_evenCols`, `evenColsBottomTail_nonblank`, `evenColsUpperSnake_nonblank`, `evenColsRoute_nonblank`, `evenColsBottomTail_nodup_cells`, `evenColsUpperColumn_nodup`, `evenColsUpperSnake_nodup`, `evenColsRoute_nodup_cells`, `evenColsRoute_nodup`, `evenColsRoute_covers` |
| `NPuzzle/Rect/EvenRowRoute.lean` | `evenRowsUpperRow`, `evenRowsUpperSnake`, `evenRowsRightColumn`, `evenRowsRouteXs`, `evenRowsUpperRow_length`, `evenRowsUpperSnake_length`, `evenRowsRightColumn_length`, `evenRowsRoute_length`, `isChain_evenRowsUpperRow`, `isChain_evenRowsUpperSnake`, `isChain_evenRowsRightColumn`, `evenRowsRoute_chain_open`, `evenRowsRoute_chain`, `evenRowsRoute_head`, `evenRowsRoute_getLast`, `evenRowsRoute_compat`, `reachable_goal_to_cfg_bottomRight_of_evenRows`, `tiles_to_goal_bottomRight_of_evenRows`, `evenRowsUpperSnake_nonblank`, `evenRowsRightColumn_nonblank`, `evenRowsRoute_nonblank`, `evenRowsUpperRow_nodup`, `evenRowsUpperSnake_nodup`, `evenRowsRightColumn_nodup`, `evenRowsRoute_nodup_cells`, `evenRowsRoute_nodup`, `evenRowsRoute_covers` |
| `NPuzzle/Rect/OddOddRoute.lean` | `oddOddRouteXs`, `oddOddLeftColumn`, `oddOddMiddleSnake`, `oddOddCapRows`, `oddOddCap`, `oddOddRoute_length`, `oddOddRoute_head`, `oddOddRoute_getLast`, `isChain_oddOddLeftColumn`, `isChain_oddOddMiddleColumn`, `isChain_oddOddMiddleSnake`, `isChain_oddOddCapRow`, `isChain_oddOddCapRows`, `isChain_oddOddCap`, `oddOddRoute_chain_open`, `oddOddRoute_chain`, `oddOddRoute_nonblank`, `oddOddRoute_nodup_cells`, `oddOddRoute_nodup`, `oddOddRoute_avoids_cornerUpLeft`, `oddOddRoute_covers`, `oddOddRoute_compat`, `reachable_goal_to_cfg_bottomRight_of_oddOdd`, `tiles_to_goal_bottomRight_of_oddOdd` |
| `NPuzzle/Rect/EvenDimension.lean` | `Board.evenDimension_or_oddRows_oddCols`, `Board.oddRows_oddCols_of_not_evenDimension`, `Board.not_evenDimension_iff_oddRows_oddCols`, `Board.size_mod_two_eq_zero_of_evenDimension`, `Board.evenDimension_iff_size_mod_two_eq_zero`, `Board.oddRows_oddCols_iff_size_mod_two_eq_one`, `Board.not_evenDimension_iff_size_mod_two_eq_one`, `no_closedFullList_of_not_evenDimension`, `reachable_goal_to_cfg_bottomRight_of_evenDimension`, `tiles_to_goal_bottomRight_of_evenDimension`, `reachable_goal_to_cfg_bottomRight_of_dimension_split`, `tiles_to_goal_bottomRight_of_dimension_split` |
| `NPuzzle/Rect/Corner.lean` | `cornerLeft`, `cornerUp`, `cornerUpLeft`, `cornerLeftIdx`, `cornerUpLeftIdx`, `cornerUpIdx`, bottom-right 2x2 adjacency/distinctness lemmas, `cornerCyclePath`, `cornerCycleCells`, `cornerCycleCfg`, `blank_cornerCycleCfg`, `cornerCycleCfg_cells_*`, `reachable_cornerCycleCfg`, `reachable_cornerCycle_blank` |
| `NPuzzle/Rect/CornerPerm.lean` | `cornerPermList`, `cornerPerm`, `cornerPerm_apply_*`, `cornerPerm_apply_of_not_corner`, `cornerPerm_isThreeCycle` |
| `NPuzzle/Rect/CornerRealizable.lean` | `cornerCycleCfg_goal_eq_relabel_cornerPerm`, `permOfCfg_cornerCycleCfg_goal`, `cornerPerm_realizable` |
| `NPuzzle/Rect/FullCyclePerm.lean` | `fullCycleList`, `fullCyclePerm`, `fullCyclePerm_isCycle`, `fullCyclePerm_support_univ`, `fullCyclePerm_sign_of_even_tileCount`, `fullCyclePerm_not_mem_alternating_of_even_tileCount`, `fullCyclePerm_not_mem_alternating_of_odd_rows_odd_cols`, `fullCyclePerm_apply_cornerUpIdx` |
| `NPuzzle/Rect/AlmostFullCyclePerm.lean` | `almostFullCycleList`, `almostFullCyclePerm`, `almostFullCyclePerm_isCycle`, `almostFullCyclePerm_support`, `almostFullCyclePerm_apply_cornerUpIdx`, `almostFullCyclePerm_sign_of_even_tileCount`, `almostFullCyclePerm_mem_alternating_of_even_tileCount`, `almostFullCyclePerm_mem_alternating_of_odd_rows_odd_cols` |
| `NPuzzle/Rect/Parity.lean` | `blankRowFromBottom`, `invStat`, `parityClass`, `targetParity` |
| `NPuzzle/Rect/Invariant.lean` | `tileList_slide_eq_erase_insert`, `invStat_slide_horizontal_mod`, `invStat_slide_vertical_mod`, `parityClass_legalStep`, `parityClass_reachable`, `reachable_imp_parity` |
| `NPuzzle/Rect/TileGlue.lean` | `config_eq_of_tileList_and_blank`, `reachable_goal_of_tileList`, `tileList_goal`, `invStat_goal`, `parityClass_goal`, `cfg_eq_goal_of_tileList` |
| `NPuzzle/Rect/TilePerm.lean` | `TileListSpec`, `mem_Icc_of_nodup_len`, `cellsOfTileList`, `configOfTileList`, `tileList_configOfTileList`, `config_eq_configOfTileList`, `tileLabelAt`, `tileListPerm`, `permOfCfg`, `tileList_eq_of_permOfCfg_eq` |
| `NPuzzle/Rect/TileSorted.lean` | `eq_range_map_succ_of_sorted`, `tileList_eq_goalTileList_of_sorted`, `tileListPerm_sorted_eq_one` |
| `NPuzzle/Rect/TileSign.lean` | `adjSwap`, `tileListPerm_bubbleRight`, `sign_tileListPerm_eq_neg_one_pow`, `invStat_even_iff_perm_alternating` |
| `NPuzzle/Rect/TileRelabel.lean` | `relabelConfig`, `reachable_relabel`, `tileListPerm_relabel`, `tileListPerm_congr`, `permOfCfg_relabel` |
| `NPuzzle/Rect/Realizable.lean` | `PermRealizable`, `permRealizableSubgroup`, `permRealizable_mul`, `permRealizable_inv`, `permRealizable_of_mem_closure` |
| `NPuzzle/Rect/AbstractSufficiency.lean` | `invStat_even_of_parity_bottomRight`, `permRealizable_mem_alternating`, `not_permRealizable_of_not_mem_alternating`, `permRealizable_of_mem_alternating_of_generators`, `permRealizable_of_mem_alternating_of_almost_generators`, `reachable_goal_to_cfg_bottomRight_of_generators`, `reachable_goal_to_cfg_bottomRight_of_almost_generators`, `reachable_goal_to_cfg_bottomRight_of_parity_generators`, `reachable_goal_to_cfg_bottomRight_of_almost_parity_generators`, `tiles_to_goal_bottomRight_of_parity_generators`, `tiles_to_goal_bottomRight_of_almost_parity_generators` |
| `NPuzzle/Rect/GeneratorSufficiency.lean` | `reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle`, `tiles_to_goal_bottomRight_of_compatibleFullCycle`, `reachable_goal_to_cfg_bottomRight_of_compatibleAlmostFullCycle`, `tiles_to_goal_bottomRight_of_compatibleAlmostFullCycle`, `reachable_goal_to_cfg_bottomRight_of_cornerLeftFullCycle`, `tiles_to_goal_bottomRight_of_cornerLeftFullCycle`, `reachable_goal_to_cfg_bottomRight_of_fullCycle`, `tiles_to_goal_bottomRight_of_fullCycle`, `reachable_goal_to_cfg_bottomRight_of_almostFullCycle`, `tiles_to_goal_bottomRight_of_almostFullCycle` |

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
| `NPuzzle/Group/CycleThree.lean` | `isPreprimitive_of_mem_full_cycle_and_three_cycle`, `alternatingGroup_le_of_mem_full_cycle_and_three_cycle`, `isPreprimitive_of_mem_almost_full_cycle_and_three_cycle`, `alternatingGroup_le_of_mem_almost_full_cycle_and_three_cycle` |

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
| **R0** | Extract group tail: full/near-full cycle + compatible 3-cycle ⇒ `alternatingGroup` | done in `NPuzzle/Group/CycleThree.lean` |
| **R2** | Move `inversionCount` + namespace `Inversion` → `NPuzzle/List/Inversion.lean` (no `Cell`) | done for `inversionCount_erase_insert_mod` and list move helpers |
| **R3** | `FourFour/Inversion.lean` keeps only puzzle glue (`invStat_slide_vertical_mod`, …) | R2 |
| **R4** | Paper §5–6: table Lean name ↔ classical lemma (Calabro sign/taxicab, Conrad $A_{15}$) | paper draft |
| **R5** | **Mathlib PR** (project intention): generalized `inversionCount_erase_insert_mod` / list move helpers | after more cleanup and Mathlib review |
| **R6** | Add `NPuzzle.Rect.Basic` / `Config` / `Parity` / `Invariant` as the first board-generic layer | necessity/parity invariance, realizable corner 3-cycle, compatible full-cycle and near-full-cycle shapes, closed-path-to-tile-cycle/sufficiency bridges, conditional named sufficiency, the even-size obstruction for prefixed full routes, odd×odd near-full route, and the closed fat-board bottom-right sufficiency dispatcher |

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
