---
bibkey: beatty2025couplingwasserstein
authors: E. Beatty; D. Stilck França
year: 2025
title: Order p quantum Wasserstein distances from couplings
doi: 10.1007/s00023-025-01557-z
url: https://arxiv.org/abs/2402.16477v2
claim: Countable pure-state coupling plans, their order-p costs and infimum distances, the trace-distance ground metric, and the open triangle-inequality question.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation
license: citation-only
triage: anchor
---

# Pure-state coupling Wasserstein distances

## Locator

- URL: https://arxiv.org/abs/2402.16477v2
- DOI: 10.1007/s00023-025-01557-z
- arXiv version 2, 11 March 2025; Annales Henri Poincaré.
- Definitions 8 and 9; equations (11), (12), (15), (16) and (81).
- Section IV.1, Proposition 23 and equation (62); Proposition 26 and equation (82); Appendix C.

The versioned definitions and quotations below are supplied in the problem
statement associated with issue
[#30901](https://github.com/the-omega-institute/trureturing/issues/30901).
No independent manuscript retrieval or additional literature search is claimed.

## Definitions and question

Definition 8 specifies a countable transport plan
$Q=\{(q_j,|\psi_j\rangle,|\phi_j\rangle)\}_{j\in J}$, with $q_j>0$ and

$$
\sum_j q_j|\psi_j\rangle\langle\psi_j|=\rho,
\qquad
\sum_j q_j|\phi_j\rangle\langle\phi_j|=\sigma.
$$

Definition 9 states: "let d be a distance on ℙℋ. Let p ≥ 1."
Equations (15) and (16) define

$$
T_p^d(Q)=\sum_jq_jd(|\psi_j\rangle,|\phi_j\rangle)^p,
\qquad
W_p^d(\rho,\sigma)
 =\left(\inf_{Q\in\mathcal Q(\rho,\sigma)}T_p^d(Q)\right)^{1/p}.
$$

Section V.2, equation (81), specializes the ground distance to

$$
d(|\psi\rangle,|\phi\rangle)
 =\frac12\bigl\||\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|\bigr\|_1
 =\sqrt{1-|\langle\psi|\phi\rangle|^2}.
$$

The introduction states:

> Although many desirable properties of these W_p^d are proven in Sec. IV, establishing a triangle inequality remains a difficult open problem.

After Proposition 23, equation (62), Section IV.1 states:

> It is as yet unclear whether or not equality holds in this equation, and establishing the conditions for equality is an important open problem, not least because this would allow us to recover the triangle inequality for W_1^d.

Appendix C states:

> the triangle inequality eludes us.

Proposition 26, equation (82), identifies the corresponding order-one dual
seminorm with half the trace norm. These definitions and question are
literature material. The three-dimensional triangle counterexample and its
proof are repository work.

## Scope of the source screen

The supplied follow-up quotation from Borsoni, arXiv:2512.01722v5,
Section 3.3.3, is "the cases p≠2 or other ground distances remain open."
The supplied Miller reference, arXiv:2609.03769, concerns order two with the
Hilbert–Schmidt ground distance. Its positive triangle result concerns a
different order and ground distance from the order-one trace-distance
counterexample here. These references have not been independently retrieved.
