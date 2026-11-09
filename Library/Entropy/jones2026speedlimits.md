---
bibkey: jones2026speedlimits
authors: Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller
year: 2026
title: "Certified randomness from quantum speed limits"
doi: 10.1103/bnrq-sp5w
url: https://arxiv.org/abs/2506.14526v3
claim: "The unnumbered conjecture after Appendix E(ii), Lemma 3 asks whether the optimized entropy is constant on fixed-difference correlation lines."
strata_touched:
  - D5/S3/Quantum/JonesAloyEntropyConstancy
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/bnrq-sp5w

Source: https://arxiv.org/abs/2506.14526v3

# Entropy constancy on fixed-difference lines

Caroline L. Jones, Albert Aloy, Gerard Higgins and Markus P. Müller,
*Certified randomness from quantum speed limits*, PRX Quantum 7, 010349.
Page numbers below refer to arXiv:2506.14526v3; the journal numbers Lemma 3
as Lemma E3.

Appendix E(ii), p. 16, immediately after Lemma 3, states verbatim:

> Indeed, we conjecture – and the numerics suggest – that $H^\star$ is constant on those lines, i.e. that we have equality in Lemma 3. However, we have not managed to prove this.

The lines have fixed $C_0-C_1$. Their center is
$((C_0-C_1)/2,-(C_0-C_1)/2)$. Lemma 3 bounds the entropy at the center
by its value at every other point on the line.

Equations (8)–(9), p. 4, use

$$F(C)=\frac{\sqrt{1+C_0}\sqrt{1+C_1}+\sqrt{1-C_0}\sqrt{1-C_1}}2,
\qquad \gamma(e)=\begin{cases}\cos(e)&e<\pi/2,\\0&\text{otherwise}.\end{cases}$$

The characterized domain is $C\in[-1,1]^2$ with $\gamma(e)\le F(C)$.
Time separation and Planck's constant are one. Equation (27), p. 14,
minimizes $\sum_i w_iH(C^i)$ subject to nonnegative probability weights,
the exact correlation means, nonnegative energy labels, the exact mean
energy and domain membership of each component. There is no upper cap
on individual energy labels.

The same page states verbatim:

> Here we assume $p(x)=1/2$ for both $x$, i.e. there is equal a priori probability for both inputs.

Thus $H(C)=\tfrac12[b((1+C_0)/2)+b((1+C_1)/2)]$, where
$b(p)=-p\log_2p-(1-p)\log_2(1-p)$ has its continuous endpoint values.
Lean reuses `D5.S3.Quantum.CloningMachine.binaryEntropyBits` for $b$.
The coordinate map and line center are inlined to avoid forwarding definitions.

`Ensemble n` records the weights, correlations and labels of a finite
hidden-variable decomposition. The minimum specification ranges over every
natural number n and uses `IsLeast` on actual objective values, retaining
attainment. The formal claim explicitly includes existence of a function
satisfying this specification, followed by constancy for every such function.
The refutation compares two of its values; it does not independently prove
global existence of the minimum function.

For $24/25\le s<1$, the boundary point is $B=(1,1-2s^2)$ and its line
center is $M=(s^2,-s^2)$, at energy $E=\arcsin(s)$. Boundary rigidity
forces every feasible objective at B to equal $b(s^2)/2$. At M an ensemble
with correlations $(s,-s),(1,1),(-1,-1)$ and weights
$s,(1-s)/2,(1-s)/2$ has objective $s b((1+s)/2)$.
The formal argument gives a gap greater than $7((1-s)/2)^2$ for every
function satisfying the minimum specification.

The independent experiment is in
`the-omega-institute/trureturing-experiments`, commit
`ccb00b5a04747b370cd920d6e2b04a8ac5d30fbe`, directory
`docs/reports/jones-aloy-entropy-constancy/`. The recorded command
`python3 docs/reports/jones-aloy-entropy-constancy/check.py` exits 0 with
`ALL_CHECKS_OK`; the SHA-256 of `check.py` is
`51ccb46c16a399ee61618021c9af1656d48d2dd35037fb352a72c7e32d85bc35`.
Its rational logarithm enclosure gives a gap greater than
$4330451/100000000$ nats at $s=24/25$. Its Pauli and interior-effect
calculations are computation, not Lean verification of physical realization.

The source's symmetry, midpoint lower bound, certified lower bounds and
classical-region constancy remain compatible with the refutation. Global
attainment, lower semicontinuity, interior persistence and a full classification
of equality fibers are not independently formalized in this module.
The literature screen is recorded in issue #23268. Completeness remains
ASSUMED-UNVERIFIED. This note contains no source software.
