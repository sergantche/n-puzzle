# Paper outline (draft)

## Working title

*Solvability of the Sliding Puzzle on an N×M Grid: Classical Criteria and a Lean Formalization*

## Abstract (idea)

Classical solvability theory from Johnson–Story (1879) through the modern `N×M` criterion, plus a machine-checked Lean proof for the 4×4 case and a roadmap toward rectangular-grid generalization.

## Structure

Tracked in [PLAN.md](../PLAN.md#paper-roadmap). Lean name mapping: [REUSE.md](../REUSE.md#paper-mapping-planned).

1. **Introduction** — puzzle, goals, contribution (formalization + survey).
2. **Problem statement** — configuration, moves, row-major list $L$, $I(L)$, $r_B$, theorem (as in README).
3. **Classical proofs** — Johnson (necessity), Story (sufficiency), parity formula.
4. **Group-theoretic view** — $S_{NM}$, $A_{NM-1}$, 3-cycles, $F = A_{15}$ for 4×4.
5. **Lean formalization** — `NPuzzle.FourFour` architecture, reuse layers A–D, what is proved, and what remains for generalization.
6. **Comparison with the literature** — Calabro $m\times n$, Conrad, encoding choices; Lean ↔ classical table.
7. **Conclusion** — 4×4 closed; general case is separate work.

## Target length

8–12 pages (expository note), not journal-length.

## Audience

Mathematicians and formalization readers; permutations assumed, Lean not required.
