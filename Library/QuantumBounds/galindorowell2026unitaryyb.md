---
bibkey: galindorowell2026unitaryyb
authors: C. Galindo; E. C. Rowell
year: 2026
title: "Unitary Yang–Baxter Operators: Towards a Classification"
doi: null
url: https://arxiv.org/abs/2608.16865
claim: "Conjecture 10.6 states that for d≥2 with 4∤d, a primitive d-th root w, a unit α, and a coefficient vector with a 0 = 1 and all coefficient norms equal to 1, whose cyclic Pauli operator is Yang–Baxter and projectively unitary, there is one sign ε∈{+1,−1} with a_{s+t}=a_sa_tw^{εαst}."
strata_touched:
  - D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation
license: citation-only
triage: anchor
---

# Galindo–Rowell, Unitary Yang–Baxter Operators

C. Galindo and E. C. Rowell, *Unitary Yang–Baxter Operators: Towards a Classification*,
arXiv:2608.16865v1 (2026), §2 and §10.2.7.

## Source statements

The §10.2 setting states: “Fix \(d\geq2\), choose a primitive \(d\)-th root”
\(w\); \(Xe_j=e_{j+1}\), \(Ze_j=w^je_j\); and
“\(R(a)=\sum_{t=0}^{d-1}a_tP^t, \qquad P=X\otimes Z\)” (before Galois
normalization, \(\sum_{t=0}^{d-1}a_t(X^t\otimes Z^{\alpha t})\)).
The compact coefficient phase torus is
“\(\mathbb T_d^{\mathrm{coef}} = \{(a_1,\ldots,a_{d-1})\in(\C^\times)^{d-1}: |a_t|=1\text{ for }1\leq t<d\}\).”

Section 2 displays the braid Yang–Baxter equation:
“\((R\otimes I)(I\otimes R)(R\otimes I) = (I\otimes R)(R\otimes I)(I\otimes R)\).”

Conjecture 10.6 (§10.2.7) states: “Let \(d\geq2\) with \(4\nmid d\), let
\(\alpha\in(\Z/d\Z)^\times\), and put \(P_\alpha=X\otimes Z^\alpha, \qquad
\tau_\alpha(s,t)=w^{\alpha st}\qquad(s,t\in\Z/d\Z)\). Suppose that
\(a=(1,a_1,\ldots,a_{d-1})\in\mathbb T_d^{\mathrm{coef}}\) and that
\(R_\alpha(a)=\sum_{t\in\Z/d\Z}a_tP_\alpha^t\) satisfies the Yang--Baxter equation and
is projectively unitary. Then \(a\) belongs to one of the two signed Gaussian torsors
for \(\tau_\alpha\): there exists \(\epsilon\in\{+1,-1\}\) such that
\(a_{s+t}=a_sa_t\tau_\alpha(s,t)^\epsilon\qquad(s,t\in\Z/d\Z)\).”

The Lean encoding uses `ZMod d` for the cyclic indices, the shift and clock matrices
on that index type, the Kronecker product for \(P_\alpha\), and the displayed braid
equation on the reassociated triple tensor product. Projective unitarity means that
a nonzero scalar multiple belongs to the matrix unitary group. The refuting instance is
\(d=15\), \(\alpha=1\), and \(a_t=w^{2t^2}\) for a primitive fifteenth root; its
polarization has exponent 4, whereas the two conjectured signs require exponents 1 and
14.

## Verification boundary

The paper records exact computations only for dimensions \(2,3,5,6,7,9,10,11\).
The arXiv record has v1 only. Searches recorded with the preregistration found no later
settlement of Conjecture 10.6; citing works not independently checked remain
ASSUMED-UNVERIFIED.

## Verified locator

- URL: https://arxiv.org/abs/2608.16865
