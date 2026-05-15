# Sliding Puzzle on an N×M Grid

## Task Definition

Consider a rectangular board with **N** rows and **M** columns, so there are **NM** cells. The cells contain **NM − 1** pairwise distinct numbered tiles labeled **1, …, NM − 1** and **exactly one empty cell** (the “blank”).

A **legal move** exchanges the blank with one of its **edge-adjacent** neighbors (up, down, left, or right). Equivalently, a tile adjacent to the blank slides into the blank, and the blank moves to that tile’s former cell.

Fix the **goal configuration**: reading the board **row by row from top to bottom**, and **within each row from left to right**, the tiles appear in increasing order **1, 2, …, NM − 1**, and the **blank is in the bottom-right corner** (row **N**, column **M**).

Starting from an arbitrary configuration that uses the same tiles and one blank, we ask whether it is possible to reach the goal configuration using only legal moves.

This repository aims to state that question in precise mathematical terms and to formalize the classical **solvability criterion** (together with its proof) in Lean 4.

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
I(L) := \left\lvert \bigl\{(k,\ell): 1\le k<\ell\le NM-1 \text{ and } L_{k}>L_{\ell}\bigr\} \right\rvert.
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

Assume $NM\ge 2$. Let $C$ be any configuration, let $L$ be its row-major tile list (skipping the blank), and let $i_b$ denote the blank’s row counted from the top. Write $M$ for the number of columns, and let $r_B$ be the blank’s row counted from the bottom, $r_B = N - i_b + 1$.

Then $C$ is solvable **if and only if** the following parity condition holds:

- If $M$ is **odd**: $I(L)\equiv 0 \pmod 2$.
- If $M$ is **even**: $I(L)\equiv r_B \pmod 2$.

This statement is the main mathematical result we intend to prove formally in Lean.
