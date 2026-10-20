---
bibkey: benykempfkribs2007observables
authors: Cédric Bény and Achim Kempf and David W. Kribs
year: 2007
title: Quantum Error Correction of Observables
doi: 10.1103/PhysRevA.76.042303
claim: Correctable observable algebras can be characterized in the Heisenberg picture without requiring recovery of the whole physical state.
strata_touched:
  - D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel
license: citation-only
triage: anchor
---

# Correctable observables rather than an entire physical state

The paper develops operator-algebra quantum error correction in the Heisenberg
picture, including hybrid quantum-classical information. It supplies detailed
proofs and extensions of the authors' earlier PRL framework. This is an existing
literature anchor, not a novelty claim for the repository.

For the concrete orthogonal-syndrome construction, the repository's
`logicalRepresentation S A = sum_j S_j A S_j^*` is a faithful star-preserving
multiplicative representation when the syndrome family is nonempty. Its unit is
the support projection P, not necessarily the identity on the whole physical
space. The restriction to any one syndrome copy is a left inverse. These
finite-matrix statements specify exactly which logical observables survive.
They do not by themselves prove the general correctable-algebra classification,
smooth bundle trivialisation, a Chern-number theorem, or an infinite-dimensional
recovery theorem.

Primary sources:
- https://arxiv.org/abs/0705.1574
- https://doi.org/10.1103/PhysRevA.76.042303

Companion announcement: C. Bény, A. Kempf and D. W. Kribs, *Generalization of
Quantum Error Correction via the Heisenberg Picture*, Physical Review Letters
98, 100502 (7 March 2007), DOI 10.1103/PhysRevLett.98.100502,
arXiv:quant-ph/0608071. The detailed PRA paper was published 2 October 2007.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.76.042303 resolves to the Physical
  Review A article titled above.
- Preprint: https://arxiv.org/abs/0705.1574 .
- The cited scope is correctable observable algebras in the Heisenberg picture;
  the repository proves only its stated finite orthogonal-syndrome instance.

## Task readout, statistical sufficiency and physical correction

Definition 8, equation (7), defines correction of an arbitrary set of
observables by one channel, on a stated input subspace. Theorem 9 specializes
to an observable algebra and characterizes it by the commutators with
compressed Kraus products. These are distinct scopes: an arbitrary operator
system is not automatically an algebra, and independently chosen correction
maps do not supply one common correction map.

The following finite calculations explain the task interface used in the
repository. They are elementary consequences of Heisenberg duality and
finite-dimensional separation, not new observable-correction theorems
attributed verbatim to the paper.

Let $\mathcal S$ be a real subspace of Hermitian matrices containing $I$.
An effect $H$ has the same expectation on every pair of density matrices
agreeing on $\mathcal S$ if and only if $H\in\mathcal S$. To see the
nontrivial direction, put $D=H-\operatorname{Proj}_{\mathcal S}H$.
If $D\ne0$, then $\operatorname{tr}D=0$ and, for sufficiently small
$\epsilon>0$, $I/d\pm\epsilon D$ are actual density matrices agreeing
on $\mathcal S$ but differing on $H$ by
$2\epsilon\operatorname{tr}(D^2)>0$. The full density-state source domain
is essential; a restricted source family uses its own indistinguishability
fibres. A future task effect $E$ after a channel $\Phi$ pulls back to
$H=\Phi^\dagger(E)$.

For operational readout, let $\mathcal A_h$ be a finite instrument,
with the classical record $h$ retained and $\sum_h\mathcal A_h$
trace preserving. An allowed binary readout is a family of output effects
$0\preceq F_h\preceq I$. Its worst-case probability error for a fixed input
effect $E$ is exactly

$$
\sup_{\rho}\left|\operatorname{tr}(E\rho)
 -\sum_h\operatorname{tr}(F_h\mathcal A_h(\rho))\right|
=\left\|E-\sum_h\mathcal A_h^\dagger(F_h)\right\|_{\mathrm{op}}.
$$

This follows by maximizing the expectation of the Hermitian difference over
density matrices. Thus exact readout requires a positive, normalized effect
lift, rather than membership in the unrestricted linear span of observable
images. The minimum over the finite product of effect intervals is attained.
For a nontrivial target projection $E$, allowing an arbitrary CPTP decoder
before the fixed measurement of $E$ gives the same optimization: any output
effect is realized by measuring it and preparing a state in the range or
kernel of $E$. This equivalence presupposes permission to use these operations.

For example, the qubit depolarizing channel
$\mathcal N_\lambda(\rho)=\lambda\rho+(1-\lambda)I/2$, with
$0<\lambda<1$, has an invertible linear Heisenberg map. Nevertheless the
sharp task $E=(I+X)/2$ cannot be read exactly from one output: its unique
linear lift $(I+X/\lambda)/2$ is not an effect. Its optimal probability
error is $(1-\lambda)/2$. Measuring $X$ attains this value; the two input
eigenstates of $X$ give the matching lower bound from their output trace
distance $2\lambda$. Linear reconstruction of statistics and a valid
single-system measurement are therefore different contracts. Repeated
preparation and estimation, when allowed, have their own sampling cost.

A multi-outcome readout requires one family $F_{h,y}\succeq0$ with
$\sum_yF_{h,y}=I$ for every record, and one common reconstruction of the
target effects. Separate binary lifting tests do not check this joint
normalization. Likewise, correction of several future observables by one
channel is the simultaneous condition of Definition 8.

The actual qutrit application in
[Purity arithmetic §79](../../docs/develop/theory/AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md#79-task-readout-on-the-actual-ambiguous-records)
uses these task permissions with the existing chronological word matrices.
It computes binary-readout errors, rather than the reference-stable
full-state diamond errors of that volume's §§59–78.
