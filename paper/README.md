# Paper: sliding-puzzle solvability criterion

Draft materials for an article on the classical `N×M` solvability criterion and its Lean 4 formalization.

## Files

| Path | Contents |
|------|----------|
| [literature.md](literature.md) | Literature survey (working notes) |
| [outline.md](outline.md) | Paper outline |
| [tex/main.tex](tex/main.tex) | LaTeX source |
| [tex/chapters/01-history.tex](tex/chapters/01-history.tex) | **Chapter 1:** history and literature through the general criterion |
| [tex/references.bib](tex/references.bib) | Bibliography |

## Build PDF

```bash
cd paper/tex
make          # requires pdflatex + bibtex
# or manually:
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

If the build fails after switching document class, run `make clean` first.

## Repository links

- Problem statement: [README.md](../README.md)
- Lean 4×4 status: [PLAN.md](../PLAN.md)
- Project goals: [GOAL.md](../GOAL.md)
