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
| **9** | **Sufficiency:** `parityClass cfg = 1 → Reachable cfg goal` | `TileCycles.lean` (`parity_imp_reachable`) | ❌ **sorry** (9b.3) |

**Theorem status:** `solvability_four_four` is **complete** except `tiles_to_goal_at_bottomRight` (one `sorry`).

---

## Step 9 — remaining work (from code comments)

`Sufficiency.lean`: large **connectivity** block — at most two configuration classes; `goal` in parity class 1.

| Substep | Content | Module | Status |
|---------|---------|--------|--------|
| **9a** | Blank grid connected; blank reachable in any `Config` | `BlankGrid.lean`, `BlankReach.lean` | ✅ |
| **9b.1** | Blank → `bottomRight` | `TileCycles.lean` (`reachable_blank_bottomRight`) | ✅ |
| **9b.2** | `tileList` + blank determine `cfg` | `TileCycles.lean` (`cells_eq_of_tileList`, `config_eq_of_tileList_and_blank`) | ✅ |
| **9b.3** | Tile macros / cycles → `tileList goal` | `TileCycles.lean` (`tiles_to_goal_at_bottomRight`) | ❌ sorry |
| **9c** | Assemble `parity_imp_reachable` | `TileCycles.lean` | ✅ (modulo 9b.3) |

---

## Agent tooling (done locally)

| Piece | Location | Status |
|-------|----------|--------|
| lean4-skills clone | `lean4-skills/` (gitignored) | ✅ |
| Cursor rule | `.cursor/rules/lean4.mdc` | ✅ |
| lean-lsp MCP | `.cursor/mcp.json` (`wsl.exe` + `uvx`) | ✅ 22 tools |
| Multi-root workspace | `~/github/cursor-workspaces/n-puzzle.code-workspace` | ✅ user setup |

**Sorry check:** `python3 lean4-skills/scripts/sorry_analyzer.py . --format=summary --report-only` → 1 sorry in `TileCycles.lean` (`tiles_to_goal_at_bottomRight`).

---

## After 4×4 (out of current scope)

- General `N×M` (separate theory / modules).
- Full README alignment (odd `M`: inversion-only criterion).

---

## Quick links

- Main theorem: `NPuzzle/FourFour/Sufficiency.lean`
- Invariant chain: `NPuzzle/FourFour/Invariant.lean`
- Build: `lake build`
