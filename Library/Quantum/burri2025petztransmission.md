---
bibkey: burri2025petztransmission
authors: Laura Burri
year: 2025
title: Entanglement fidelity of Petz decoder for one-shot entanglement transmission
doi: null
url: https://arxiv.org/abs/2502.17411v1
claim: Question 1 asks which of the actual Schumacher-Westmoreland and ordinary Petz decoders performs better; two source-faithful instances have opposite strict entanglement-fidelity comparisons.
strata_touched:
  - D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity
  - D5/S3/Quantum/Recovery/BurriReplacementDecoder
  - D5/S3/Quantum/Recovery/BurriReverseSource
  - D5/S3/Quantum/Recovery/BurriReverseCompletion
  - D5/S3/Quantum/Recovery/BurriReverseFidelity
  - D5/S3/Quantum/Recovery/BurriDecoderComparison
license: citation-only
triage: theorem
---

# SW and ordinary Petz need not have a uniform order

The source is Laura Burri's arXiv:2502.17411v1, not a later journal text.
Section 3.3, Question 1 asks: **“Which performs better: the SW decoder or the Petz decoder?”**
Section 3.1 and Theorem 1 explicitly construct and discuss SW for every
$(\rho,\mathcal N)\in\mathcal S(A)\times\mathrm{CPTP}(A,B)$.
The domain therefore includes nonuniform input densities. The flat code states
of the numerical examples do not restrict that domain.

Section 2.3 uses squared fidelity against a purification for entanglement
fidelity. Appendix A.6 specifies the transposed product of the two positive
roots; A.9 fixes the physical purification and ancilla relation; A.11–A.13
specify the actual Kraus construction and its composition with preparation.
The ordinary Petz decoder is Section 3.2's reference-state Petz map, including
its trace-preserving completion. Both examples below have full output support,
so the completion term is proved to vanish on every matrix.

The owning [Scribe](../../Blueprint/D5/S3/Quantum/Recovery/BurriDecoderComparison.scribe.cs)
gives the data, normalization and exact source bridges. Its common fidelity uses
$v(r,i)=(\sqrt\rho)_{i,r}$ and
$F_e(\rho,C)=\langle v|(\mathrm{id}\otimes C)(|v\rangle\langle v|)|v\rangle$.
The reference marginal is proved to be $\rho$, including for complex Hermitian
states. A proved tensor flip transports the reverse calculation to this same
definition.

| Instance | Ordinary Petz | SW |
| --- | --- | --- |
| $\rho=\operatorname{diag}(2/3,1/3)$, replacement channel into dimension one | $1/3$ | $11/27$ |
| $\rho=I_2/2$, the explicit six-dimensional positive-amplitude channel | $27/31$ | strictly below $27/31$ |

Every complex coisometric positive-polar completion has the same physical
prepared decoder action in each instance. The statements retain the literal
source environment, the full SVD and all zero coordinates. They do not assert
equality of arbitrary off-support unitary completions.

## Related primary results and scope

Sun Woo P. Kim, *Optimal recovery for quantum error correction*,
[arXiv:2603.06520v1](https://arxiv.org/html/2603.06520v1), Proposition 3,
Eqs. (20)–(22), and Corollary 4 already identify Petz posterior sampling and SW
squared-posterior sampling for CSS codes under Pauli noise. This is related
forward coverage; the paper's recovery-optimality discussion distinguishes
threshold optimality from finite-instance fidelity. Its supplement,
Eqs. (S21)–(S25), constructs the SVD recovery and requires matching preparation
and basis conventions before transferring a decoder identity.

Raban Iten, Joseph M. Renes and David Sutter, *Pretty good measures in quantum
information theory*, [arXiv:1608.08229v2](https://arxiv.org/html/1608.08229v2),
Section 3.3 after Eq. (54), give the pretty-good singlet-recovery optimality
criterion $[\tau_{AC},I_A\otimes\operatorname{tr}_A\sqrt{\tau_{AC}}]=0$.
That criterion alone does not prove strict loss of the actual SW construction.

The bounded standing check also read arXiv:2410.23622v5, Theorem 2 and
Corollary 1; arXiv:2602.14732v1, Section 5.3, Theorem 29; and
arXiv:2610.31501v1, Theorem 3.1. These checked passages do not furnish the exact
two-instance no-order result. This is not an exhaustive citation search or a
global novelty claim. The publisher article was inaccessible to that check;
its wording is not authenticated here.

Question 2 separately compares a SW lower bound and a Petz Renyi-information
expression. No answer to Question 2, uniform strict advantage, or complete
classification is claimed.
