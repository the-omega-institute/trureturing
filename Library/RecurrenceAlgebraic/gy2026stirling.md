---
bibkey: gy2026stirling
authors: René Gy
year: 2026
title: "On Certain Products of Three Stirling Numbers"
doi: 10.5281/zenodo.22082106
url: https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16
claim: "Section 5 asks whether strong coefficientwise q-log-concavity of the inputs forces coefficient log-concavity of both symmetric triple-product differences."
strata_touched:
  - D5/S3/Arith/PolynomialValues/GyC51Settlement
license: CC-BY-4.0
triage: anchor
---

# René Gy on Stirling triple-product differences

## Verified locator

René Gy, *Integers* 26 (2026), A108. The definition of the input order and the
two triple-product differences are on printed p. 15. The unnumbered question
is on printed p. 16 in §5. [Definitions](https://math.colgate.edu/~integers/aa108/aa108.pdf#page=15) · [Question](https://math.colgate.edu/~integers/aa108/aa108.pdf#page=16) · [DOI 10.5281/zenodo.22082106](https://doi.org/10.5281/zenodo.22082106)

## Published question

> More generally, one may ask whether it holds that if $(x_k)_{k\ge1}$ is a strongly $q$-log-concave sequence of polynomials in $\mathbb R[q]$, then, for each particular choice of $n$, $p$, and $j$, the sequences of coefficients of the polynomials $E_x^{n,p,j}(q)$ and $H_x^{n,p,j}(q)$ are themselves log-concave.

The question uses the two polynomials defined in Conjecture 5.1 for
`1 ≤ j ≤ p ≤ n`. Its input condition compares coefficients of
`x_i x_r − x_(i−1) x_(r+1)` for `r ≥ i−1 ≥ 0`. Terms in the symmetric
polynomials start at `x_1`. The elementary sum uses subsets of the
indicated size, and the complete homogeneous sum uses multisets of that
size. Their degree-zero terms are one. Conjecture 5.1 asks for coefficient
nonnegativity of these differences.

## Attribution and license

Gy supplies the question and definitions. The preregistered Codex CLI research
flight developed the counterexample family, and the Codex CLI Lean probe
formalized it. The preregistration credits the GPT Pro literature search and
Claude Code coordination. Zenodo record 22082106 lists the identical journal
PDF under CC BY 4.0. [Producer credits](https://github.com/the-omega-institute/trureturing/issues/31896) · [Version record](https://zenodo.org/records/22082106) · [License](https://creativecommons.org/licenses/by/4.0/)

## Related results

The literature check in the preregistration identified Gy's scalar positivity
argument in Theorem 3.1, his follow-up on monomial positivity, Sagan's
symmetric-function index inequalities, and Sagan–Swanson's bottom-heaviness
conjecture for $q$-Stirling families. The check found no settlement of the
arbitrary-input coefficient question within those sources. [Preregistration and literature check](https://github.com/the-omega-institute/trureturing/issues/31896) · [Gy's follow-up](https://zenodo.org/records/22960306) · [Sagan](https://doi.org/10.1090/S0002-9947-1992-1066448-X) · [Sagan–Swanson](https://arxiv.org/abs/2205.14078)
