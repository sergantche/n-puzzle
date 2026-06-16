# Sliding Puzzle on an N×M Grid

## Task Definition

Consider a rectangular board with **N** rows and **M** columns, so there are **NM** cells. The cells contain **NM − 1** pairwise distinct numbered tiles labeled **1, …, NM − 1** and **exactly one empty cell** (the “blank”).

<img src="assets/puzzle%20shuffled.png" alt="Arbitrary 3×3 sliding-puzzle configuration (example)" width="251">

_Figure 1._ An arbitrary **3×3** configuration.

A **legal move** exchanges the blank with one of its **edge-adjacent** neighbors (up, down, left, or right). Equivalently, a tile adjacent to the blank slides into the blank, and the blank moves to that tile’s former cell.

Fix the **goal configuration**: reading the board **row by row from top to bottom**, and **within each row from left to right**, the tiles appear in increasing order **1, 2, …, NM − 1**, and the **blank is in the bottom-right corner** (row **N**, column **M**).

<img src="assets/puzzle%20solved.png" alt="Goal configuration on a 3×3 board (tiles 1–8 in order, blank bottom-right)" width="251">

_Figure 2._ The **goal configuration** on **3×3**: tiles **1…8** in row-major order, blank bottom-right.

Starting from an arbitrary configuration that uses the same tiles and one blank, we ask whether it is possible to reach the goal configuration using only legal moves.

This repository aims to state that question in precise mathematical terms and to formalize the classical **solvability criterion** (together with its proof) in Lean 4.  
**Goals:** [GOAL.md](GOAL.md) · **Plan:** [PLAN.md](PLAN.md) · **Reusable modules:** [REUSE.md](REUSE.md).

## Formalization

### Board and goal

Identify cells with pairs $(i,j)$ where $i\in\{1,\ldots,N\}$ is the **row index from the top** and $j\in\{1,\ldots,M\}$ is the **column index from the left**.

A **configuration** consists of:

- a distinguished **blank cell** $(i_b,j_b)$, and
- a bijection from the set of **non-blank** cells to $\{1,\ldots,NM-1\}$ assigning the **tile number** in each such cell.

The **goal configuration** $G$ is the configuration whose blank is $(N,M)$, and whose tile at $(i,j)\neq(N,M)$ equals the **row-major index** of $(i,j)$ among all cells except $(N,M)$: concretely, the tile numbers read in row-major order are $1,2,\ldots,NM-1$.

### Row-major traversal and the induced tile list

Linearly order the cells by **row-major order**: $(i,j)\prec(i',j')$ if $i<i'$, or ($i=i'$ and $j<j'$).

Given a configuration, list the tile numbers by visiting non-blank cells in increasing $\prec$-order (equivalently: scan row-major and **skip** the blank). This yields a finite sequence

$$
L = (L_{1},\ldots,L_{NM-1}),
$$

which is a permutation of $\{1,\ldots,NM-1\}$.

### Inversion count

For a sequence $L=(L_{1},\ldots,L_{NM-1})$, define the **inversion count**

$$
I(L) := |\{(k,\ell): 1\le k<\ell\le NM-1 \text{ and } L_{k}>L_{\ell}\}|.
$$

### Blank row counted from the bottom

If the blank lies in row $i_b\in\{1,\ldots,N\}$ (counted from the **top**), define

$$
r_B := N - i_b + 1 \in \{1,\ldots,N\},
$$

the **row index of the blank counted from the bottom** ($r_B=1$ on the bottom row, $r_B=N$ on the top row).

### Solvability

A configuration $C$ is **solvable** if there exists a finite sequence of legal moves that transforms $C$ into the goal configuration $G$.

### Target theorem (solvability criterion)

Assume $NM\ge 2$. Let $C$ be any configuration, let $L$ be its row-major tile list (skipping the blank), and let $r_B := N - i_b + 1$ for its blank as in the preceding subsection — relative to the goal configuration $G$ described above.

Then $C$ is solvable **if and only if**:

- If $M$ is **odd**: $I(L)\equiv 0 \pmod 2$.
- If $M$ is **even**: $I(L)+r_B\equiv 1 \pmod 2$.

This statement is the main mathematical result we intend to prove formally in Lean.

## Lean layout

- **`lakefile.toml`** — Lake project; depends on [Mathlib](https://github.com/leanprover-community/mathlib4).
- **`NPuzzle.lean`** — root of the `NPuzzle` library.
- **`NPuzzle/FourFour/`** — 4×4 formalization (see [PLAN.md](PLAN.md) for the proof checklist).
- **`NPuzzle/FourFour/Sufficiency.lean`** — target theorem `solvability_four_four`.
- **`NPuzzle/Rect/Thin.lean`** — thin-board `tileList` criteria `solvability_rows_lt_two` / `solvability_cols_lt_two`.
- **`NPuzzle/Rect/EvenDimension.lean`** — rectangular fat-board theorem `solvability_of_two_le` for `2 ≤ rows` and `2 ≤ cols`.
- **9b.3 (closed):** `TilePerm.lean`, `TileRank.lean`, `TileSign.lean`, `TileReach.lean`, `TileRelabel.lean`, `TileConnectivity.lean` — tile-list permutations, even-permutation realization, and connectivity with the blank at bottom-right.

Build the library: `lake build`.

**Paper and literature:** [paper/](paper/).

### 4×4 status (`NPuzzle.FourFour`)

For even width **M = 4**, the README criterion is  
`(I(L) + r_B) ≡ 1 (mod 2)` ⟺ reachability of the standard goal.

| Part | Status |
|------|--------|
| Definitions (`Config`, `tileList`, `invStat`, `parityClass`, `Reachable`) | Done |
| Necessity: reachable ⇒ correct parity | Done |
| Blank geometry (blank can be moved anywhere) | Done |
| `tileList` + blank position determine the board | Done |
| `invStat = 0` with blank bottom-right ⇒ already `goal` | Done |
| Corner 3-cycle slide macro from `goal` | Done |
| `TileInverse` — slide inverse / `Reachable` symmetry | Done |
| `TilePerm` / `TileRank` — `tileListPerm`, `permOfCfg`, ranks | Done |
| `TileSign` — `sign (tileListPerm) = negOnePow (inversionCount)`; even `invStat` ↔ `A₁₅` | Done |
| `TileReach` — `PermRealizable`, `reachable_goal_to_cfg_bottomRight` | Done |
| `TileConnectivity` — `tiles_to_goal_at_bottomRight` | Done |
| **Sufficiency:** correct parity ⇒ reachable `goal` | **Done** |

The statement `solvability_four_four` is fully proved in Lean, and the dependency chain builds (`TileSign` → `TileReach` → `TileConnectivity` → `Sufficiency`) without `sorry` on the 4×4 critical path. The last group-theoretic step is `permRealizable_of_mem_alternating` in `TileReach.lean`: every even permutation of the 15 tiles is realized from `goal` with the blank at bottom-right. Details: [PLAN.md](PLAN.md).
