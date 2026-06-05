# Project goals

**Living documents:** [GOAL.md](GOAL.md) (why and what success looks like) · [PLAN.md](PLAN.md) (proof checklist and roadmaps) · [REUSE.md](REUSE.md) (what others can import).

## In one paragraph

Formally prove the classical **solvability criterion** for the sliding puzzle on a rectangular grid in **Lean 4**, and turn the effort into **checkable, reusable** artifacts: code, literature survey, and paper. Current focus: the **4×4** special case.

## Why we are doing this

1. **Mathematics.** Classical theory starts with Johnson–Story (1879): necessity, sufficiency on 4×4, and the start of rectangular boards; the modern N×M criterion is their classification plus later packaging (Archer, Calabro, and others). “Clear on paper” ≠ “machine-checked” — the goal is a closed proof with no gaps on the critical path.

2. **Formalization as a product.** Not only the end theorem, but **layers others can import** without copying the whole 4×4 proof. See [REUSE.md](REUSE.md) for the import surface; see [PLAN.md](PLAN.md#reuse--extraction-roadmap) for extraction steps.

   | Layer | Content | Status |
   |-------|---------|--------|
   | **A — List combinatorics** | `inversionCount`, adjacent swap / `eraseIdx`–`insertIdx` parity (`Inversion` namespace) | ✅ green (still under `FourFour` path) |
   | **B — Move ↔ list ↔ sign** | how slides change `tileList`; `parityClass` necessity; `sign` ↔ `invStat` ↔ `A_n` (`Invariant`, `TileListVertical`, `TileSign`, `TilePerm`) | ✅ green |
   | **C — Blank geometry** | blank connectivity, glue `cfg` ↔ `tileList` (`BlankGrid`, `BlankReach`, `TileGlue`) | ✅ green, 4×4-specific encoding |
   | **D — Sufficiency** | `PermRealizable`, corner macros, `tiles_to_goal_at_bottomRight` | ❌ 1 `sorry` on critical path |

   **Delivery forms (planned):** Lake dependency + [REUSE.md](REUSE.md); paper chapter mapping Lean names ↔ classical lemmas; later optional `NPuzzle.List` split and Mathlib PR for layer A only.

3. **Publication.** An expository paper plus repository: what is proved, what remains, and how it connects to the classics (Archer, Calabro, Mathlib). Paper roadmap: [PLAN.md](PLAN.md#paper-roadmap), draft in [paper/](paper/).

## What counts as success

| Level | Criterion |
|-------|-----------|
| **Minimum (4×4)** | `solvability_four_four` builds **without `sorry`**; README and PLAN stay current. |
| **Useful to others** | [REUSE.md](REUSE.md) documents green modules and stable lemmas; honest `sorry` status in the repo. |
| **Reuse hygiene** | Layer A split to `NPuzzle.List` (no `Cell` dependency); consumers can `require` this repo without puzzle glue. |
| **Extension (later)** | General N×M — separate phase; does not block 4×4. Mathlib PR for list-inversion lemmas — only if layer A stabilizes and Mathlib wants it. |

## Out of scope (for now)

- Optimal solving algorithms or complexity bounds (Calabro et al. — reference only).
- Full Wilson/Archer formalization “as on paper” — we use what fits Mathlib and our encoding.
- Graph and non-rectangular boards (hex, etc.).
- Publishing layer D (`TileReach`, `TileMacros`) as reusable API until the `sorry` is closed.

## Current focus

- **Lean:** close `permRealizable_of_mem_alternating` in `TileReach.lean` — the only `sorry` on the sufficiency path. Details: [PLAN.md](PLAN.md).
- **Paper:** chapter 1 done; next: problem statement, criterion, formalization chapter. Details: [PLAN.md](PLAN.md#paper-roadmap).
- **Honesty:** do not claim the theorem is fully proved while any `sorry` remains.

## Related files

- [README.md](README.md) — problem statement and criterion
- [PLAN.md](PLAN.md) — formalization checklist, reuse roadmap, paper roadmap
- [REUSE.md](REUSE.md) — import guide for reusable Lean modules
- [paper/](paper/) — literature notes and LaTeX draft
