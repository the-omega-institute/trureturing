---
bibkey: aloy2024threeoutcomepibi
authors: A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel
year: 2024
title: "Deriving three-outcome permutationally invariant Bell inequalities"
doi: 10.3390/e26100816
url: https://arxiv.org/abs/2406.11792v1
claim: "Section III.A proposes five Table III Bell inequalities for every N > 3 and asks for proofs of their validity for arbitrary party number."
strata_touched:
  - D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.3390/e26100816

Source: https://arxiv.org/abs/2406.11792v1

# Three-outcome permutationally invariant Bell inequalities

A. Aloy, G. Müller-Rigat, J. Tura and M. Fadel, *Deriving three-outcome
permutationally invariant Bell inequalities*, Entropy 26 (2024), 816.
The locators below refer to arXiv:2406.11792v1.

The scenario has N parties, two inputs per party and three outcomes. Equation (3),
p. 2, defines the PI one-party observable as the sum of marginal probabilities and
the PI two-party observable as the sum over ordered distinct parties. Equation (19),
p. 5, gives the five symmetrized observables; Eq. (20) gives their Bell expression.
Table II gives the deterministic outcome-pair count formulas.

Section III.A, p. 5, states verbatim:

> To give a concrete example, we propose for any $N>3$ the five 3PIBIs shown in Tab. III.

> At this point, for each conjectured inequality we have to prove that it is indeed valid for arbitrary number of parties $N$, or at least for all $N$ larger than a minimum number.

Table III, p. 6, lists the coefficient rows in the order
$(\alpha_1,\alpha_2,\alpha_3,\alpha_4,\alpha_5,\beta_c)$:

| Row | Coefficients |
| --- | --- |
| 1 | $(1,1,0,-2,0,0)$ |
| 2 | $(1,1,-2,-2,2,0)$ |
| 3 | $(-2,1,2,2,0,4)$ |
| 4 | $(-6,1,4,4,2,12)$ |
| 5 | $(-6,1,4,0,0,24)$ |

The Lean definitions retain the literal observable sums and coefficient rows.
The hidden variable has a finite type L, with normalized nonnegative real weights
w and local response probabilities p. Parties, inputs and outcomes use Fin N,
Fin 2 and Fin 3. The two-party observable excludes the equal-party term.
The finite model is the finite convex-hull formulation; the module does not prove
an integral representation theorem for arbitrary measurable hidden variables.
The claim asks for all five inequalities when N > 3. Their new proof is assessed
as repository-derived with this note acknowledging the source of the proposal.
Validity does not by itself establish facetness or a quantum violation.
