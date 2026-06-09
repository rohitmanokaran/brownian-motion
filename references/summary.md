# References

<!-- archon:references-summary -->
<!-- One row per file. Agents append/update rows as they discover what -->
<!-- actually works. The `How to read` column is a LIVING LOG, not a -->
<!-- static cheat-sheet — fill it in the first time you successfully -->
<!-- ingest a file, and correct it if a later attempt finds a better way. -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `../README.md` | Project overview: Brownian motion is complete and being upstreamed; stochastic integration and Itô's lemma are ongoing. It also identifies the Brownian-motion preprint and project resources. | From the project root: `sed -n '1,220p' README.md`. |
| `../Manuscript/proof_outline.tex` | Detailed informal proof outline for the Brownian-motion formalization, covering probability preliminaries, separating algebras and characteristic functions, Gaussian variables, projectivity, and Kolmogorov–Chentsov continuity. | From the project root: `sed -n '1,260p' Manuscript/proof_outline.tex`; section discovery also works with `rg -n '^\\(section|subsection)' Manuscript/proof_outline.tex`. |
| `../blueprint/src/content.tex` | Blueprint entry point. It records the completed Brownian-motion part and the ongoing stochastic-integral part, and lists the chapter files for each. | From the project root: `sed -n '1,240p' blueprint/src/content.tex`; open the referenced files under `blueprint/src/chapters/` for theorem-level prose. |

<!-- Rules of thumb when filling in `How to read`:                       -->
<!--   * If `Read` worked out of the box, write `Read` (and any options   -->
<!--     you needed, e.g. `pages: "1-5"` for long PDFs).                  -->
<!--   * If `Read` failed and you fell back to a shell command, record   -->
<!--     the exact command (e.g. `pdftotext file.pdf -`, `pandoc … -t    -->
<!--     markdown`, `unzip -p archive.zip path/inside.tex`).             -->
<!--   * If a file is binary / opaque (e.g. a Mathematica notebook with  -->
<!--     no useful plain-text export), say so — that saves the next      -->
<!--     agent from trying.                                              -->
<!--   * When in doubt, prefer the cheapest tool that gives you the part -->
<!--     you actually need (a page range, a single table) over loading   -->
<!--     the whole file.                                                 -->
