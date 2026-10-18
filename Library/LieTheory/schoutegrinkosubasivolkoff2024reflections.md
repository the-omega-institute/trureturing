---
bibkey: schoutegrinkosubasivolkoff2024reflections
authors: Eddie Schoute, Dmitry Grinko, Yiğit Subaşı, Tyler Volkoff
year: 2024
title: Quantum Programmable Reflections
doi: 10.48550/arXiv.2411.03648
url: https://arxiv.org/abs/2411.03648v2
claim: Section 4.2.1, Conjecture 4.6 asks for probe probabilities giving a flat spectrum for every copy number; equation (183) states the equivalent Clebsch–Gordan system.
strata_touched:
  - D5/S3/Quantum/Measurement/SGVFlatSpectrum
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2411.03648

Source: https://arxiv.org/abs/2411.03648v2

The arXiv record identifies version 2, submitted 17 June 2026, and lists no journal DOI.

## Statements

Section 4.2.1, page 36:

“Conjecture 4.6. The probabilities q_j for j ∈ {(n mod 2)/2, …, n/2} in Eq. (181), which define the probe state Φ_n, could be chosen such that ‖|v_J⟩‖² = 1/binom(n+2, 2) (182) for every J ∈ {(n mod 2), …, n − 2, n}.”

“The reason for this conjecture is the following: we observe numerical solutions {q_j}_j for different n ≤ 60 of the following linear system”

$$
\frac{2J+1}{\binom{n+2}{2}}
=\sum_{j\geq J/2}\frac{q_j}{2j+1}
  \left|\sum_{m=-j}^{j}C^{J0}_{jm,j-m}\right|^2
\tag{183}
$$

“for all J ∈ {(n mod 2), …, n − 2, n}.”

## Encoding and boundary

The spins and magnetic projections in Racah's Condon–Shortley formula are doubled integers. Its admissibility conditions and finite summation range are explicit. Integer division in the factorial arguments is Euclidean division, and a factorial argument x is read as `Nat.factorial x.toNat`. The coefficient owner is `D5.S3.Quantum.Decoherence.DampedSpinKernelPositivityRefutation.CG`. The equality with the displayed Racah expression, on the admissible summation inputs, is proved inside `equal_spin_coefficient`.

The probability index k corresponds to j = n/2 − k, with 0 ≤ k ≤ ⌊n/2⌋. All subtractions in `n - 2 * k` and in the binomial arguments are natural subtraction. A term is zero when J > n − 2k. The real coefficient is squared, as in equation (183).

The repository construction is

$$
q_{n/2-k}=\frac{(n-2k+1)^2\binom{2n-2k+1}{n-k}\binom{2k}{k}}
 {4^n\binom{n+2}{2}}.
$$

The proof establishes nonnegativity, normalization and every equation (183) for all n ≥ 1. Strict positivity is a private supporting result. Uniqueness and the polynomial connection formulas are outside the formal statement. Corollary 4.7's entropy expression and the qubit lower bound in Theorem 4.10 follow as consequences within the source's arguments; those arguments are not formalized in this module.
