---
slug: debrota-2017-hoggar-sic-sum-negativity
bibkey: debrota2017negativity
doi: 10.1007/s10701-017-0098-z
url: https://arxiv.org/abs/1703.08272v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/HoggarSicSumNegativity.result
---

# The sharp Hoggar-SIC sum negativity is seven eighths

## Problem

John B. DeBrota and Christopher A. Fuchs, *Negativity Bounds for
Weyl–Heisenberg Quasiprobability Representations*, arXiv:1703.08272v2,
Section 6, page 17, write:

> Although dimension $5$ was the last in which we were able to explicitly calculate the sum negativity for the SIC Q-reps by exhaustive combinatorial searching, we suspect that we have found the correct sum negativity for $\{Q_j^-\}$ constructed with the Hoggar SIC in dimension $8$. Rather than calculating the eigenvalues of every partial sum matrix (since this is infeasible for $2^{64}$, $8\times8$ matrices), we used a numerical local maximization procedure and around $10^6$ random pure state seeds. The overall maximum value we found, $7/8$, occurred frequently in our data and is significantly larger than all of the smaller local maxima. Of course, we could still be falling short of the global maximum value if it occurs at very hard to access positions. The states whose quasiprobability representations achieve the sum negativity of $7/8$ consist of $28$ copies of value $-1/32$ and $36$ copies of value $5/96$.

The precise question, preregistered in issue #11512, is whether $7/8$ is
the attained greatest value of sum negativity over all density matrices.
With the three-qubit Pauli orbit of
$v=(-1+2i,1,1,1,1,1,1,1)^T$, write
$\Pi_j=u_ju_j^*/12$, $Q_j^-=3\Pi_j-I/4$ and
$q_\rho(j)=\operatorname{Re}\operatorname{Tr}(\rho Q_j^-)/8$.
Equations (8)–(11) define
$N^1(\rho)=\sum_j(|q_\rho(j)|-q_\rho(j))/2$ and maximize it over
positive-semidefinite complex $8\times8$ matrices of trace one.

## Motivation

The frozen declaration
`D5/S3/Quantum/Measurement/HoggarSicSumNegativity.result` gives an upper
bound for every density matrix and an explicit pure state attaining it.
Thus the numerical value in Section 6 is the global maximum, including
mixed states. The source relates negativity bounds to quasiprobability
representations and quantum contextuality.

## Gap

Issue #11512 classifies the question as Tier 1 and records the bounded
literature check before the probe: searches of the ten listed citing
arXiv sources for sum negativity, Hoggar and $7/8$ found no proof of this
bound; the arXiv abstract queries returned four sum-negativity papers and
only the source for Hoggar with negativity. The issue also records MathDB
and formal-conjectures searches without a matching settlement.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Kernel computation over Gaussian integers proves that all orbit vectors
   have squared norm 12 and all 4096 squared overlaps are 144 on the
   diagonal and 16 off it. Transport to complex matrices gives the SIC
   overlaps and positive-semidefinite trace-one projectors.
2. The $64$ matrices $Q_j^-$ satisfy
   $\operatorname{Tr}(Q_j^-Q_k^-)=8\delta_{jk}$ and form a basis of the
   $64$-dimensional complex matrix space. Recovering the basis coefficients
   yields $\sum_jq_\rho(j)=1$ and
   $\sum_jq_\rho(j)^2=\operatorname{Tr}(\rho^2)/8$.
3. Positivity gives $q_\rho(j)\ge-1/32$. Nonnegative eigenvalues and trace
   one give $\operatorname{Tr}(\rho^2)\le1$.
4. For $t\ge-1/32$ the quadratic majorant
   $g(t)=\frac92(t-\frac5{96})^2$ bounds $\max(0,-t)$.
   Summing gives $N^1(\rho)\le7/8$.
5. For $w=\bar v$, the density matrix $ww^*/12$ has 28 coordinates
   $-1/32$ and 36 coordinates $5/96$, so $N^1=7/8$.

## Falsifier

A density matrix in the specified representation with sum negativity
greater than $7/8$, or failure of attainment, would falsify the source
claim. Both are excluded by the kernel-checked `result`. Replacing the
Q-minus convention, the factor $1/8$, or the Hoggar orbit changes the
question; the theorem makes no assertion about those replacements.

## Evidence

The canonical source is
`D5/S3/Quantum/Measurement/HoggarSicSumNegativity.lean`; the only public
theorem is `result : claim`. `claim` is an `IsGreatest` assertion with
membership and a universal upper bound. Its public definitions specify
the Gaussian-integer sign table and fiducial orbit (`bitSign`, `orbitG`),
the vector, projector, Q-minus operator, real quasiprobability coordinate,
negative part and sum negativity. The complex trace is real on the
density-matrix domain, as proved inside the bound.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`.
The exact finite certificates use `decide +kernel`; there is no
`native_decide`, `sorry`, or new axiom. The sole private theorem
`sic_negativity_bound` constructs the basis, Parseval identity, purity
estimate and majorant bound; elementary rewrites remain inside `result`.

## Triage

Tier 1 published conjectural value; resolution `Proved` by
`D5/S3/Quantum/Measurement/HoggarSicSumNegativity.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(issue #11512). Utility `none`: finite computations certify frame
identities and attainment for a universal theorem over density matrices.

### What the settlement shows

- **Proved in this module:** trace orthogonality supplies completeness
  and Parseval; positivity and trace one supply the purity bound. The
  majorant combines these constraints into a sharp $7/8$ global bound.
- **Proved in the private bound:** the upper bound needs only 64
  positive-semidefinite trace-one projectors in dimension eight with
  pairwise trace overlaps $1/9$. The proof therefore bounds any such SIC
  Q-minus representation by $7/8$. Attainment for other SICs is open in
  this module.
- **Proved inside `result`:** the explicit conjugate-fiducial state
  attains the bound with precisely the two values reported in Section 6.
  The theorem does not classify all attaining states.
- **Open as a separate formal consequence:** Section 6 invokes the
  paper's Theorem 3 to infer local maximality among all Q-reps if the
  stated two-value states attain the true maximum. This module establishes
  that premise; Theorem 3 and the local-maximality conclusion are not
  formalized here. The source's broader questions about non-Hoggar SICs,
  covariance, entropy and other negativity norms remain open here.
- **Open follow-up:** characterize equality in the majorant and purity
  estimates and determine which other dimension-eight SICs attain $7/8$.
  No additional theorem is included in this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent solution. The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper is
checked by reading the source, definitions and mirror. Unitary or
antiunitary equivalence of alternate Hoggar realizations and a complete
classification of maximizing states are not formalized in this module.
