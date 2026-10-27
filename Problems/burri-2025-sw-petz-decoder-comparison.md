---
slug: burri-2025-sw-petz-decoder-comparison
bibkey: burri2025petztransmission
doi: null
url: https://arxiv.org/abs/2502.17411v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Recovery/BurriDecoderComparison.result
---

# Burri's SW–Petz decoder comparison

## Problem

Laura Burri, *Entanglement fidelity of Petz decoder for one-shot entanglement
transmission*, arXiv:2502.17411v1, Section 3.3, Question 1 asks:

> Which performs better: the SW decoder or the Petz decoder?

The source domain is every density state and CPTP noise channel (Section 3.1,
Theorem 1). The question concerns the actual Appendix A SW decoder and ordinary
Petz decoder, measured by canonical entanglement fidelity. It is separate from
Question 2's comparison with a lower bound.

## Motivation

The question compares two concrete recovery constructions on the full source
domain, while the numerical examples in the source use flat code states. A
faithful answer must retain the physical isometry, source environment, SVD and
completion data, and must compare both constructions through one canonical
entanglement-fidelity definition.

## Gap

Question 1 does not specify a uniform ordering. The bounded checked primary
sources and the related literature in the [literature entry](../Library/Quantum/burri2025petztransmission.md)
do not provide this exact unrestricted two-instance comparison. This dossier
does not claim an exhaustive citation search or global novelty.

## Route

Use two source-faithful Appendix A instances with opposite strict comparisons.
The common root vector is $v(r,i)=(\sqrt\rho)_{i,r}$ in reference-first order;
its pure density is normalized and has channel-input marginal $\rho$. The
reverse calculation is transported by an actual tensor-order reindexing of the
vector, density and channel extension, including the reverse factor flip.

## Falsifier

The settlement would fail if either encoded instance did not satisfy the source
domain, if the ordinary Petz completion or the SW preparation were not proved
for the literal physical construction, if the two fidelity expressions used
different input states or roots, or if either strict inequality failed. A claim
that one decoder uniformly dominates the other would also be incompatible with
the two certified opposite witnesses.

## Evidence

The [owning Scribe](../Blueprint/D5/S3/Quantum/Recovery/BurriDecoderComparison.scribe.cs)
contains the full instance data and cites the physical construction proofs.
For the first instance, $A=\mathrm{Fin}\,2$, $B=\mathrm{Fin}\,1$,
$E=A\times B$ and $\rho=\operatorname{diag}(2/3,1/3)$. The isometry sends
$|i\rangle$ to $|0\rangle_B|i,0\rangle_E$. The normalized correlated root
vector supplies the fixed ancilla and $W=I$. SW has fidelity $11/27$, ordinary
Petz has fidelity $1/3$, and their gap is $2/27$. This uses the existing
`BurriReplacementDecoder` source, including its full-channel Petz
identification and supported-action uniqueness.

For the second instance, $A=\mathrm{Fin}\,2$,
$B=\mathrm{Fin}\,2\times\mathrm{Fin}\,3$, $E=A\times B$ and $\rho=I_2/2$.
The positive $6\times6$ matrix $Y$ gives physical Kraus operators
$K_a(b,i)=Y((i,a),b)/\sqrt{31}$, retaining the full twelve-dimensional
environment, with output $Y^2/62$. Ordinary Petz has fidelity $27/31$; the
actual SW fidelity is strictly smaller by an exact radical sum-of-squares
certificate. The seven `BurriReverse*` modules prove the isometry, state,
marginals, positive roots, literal source matrix, full SVD with eighteen null
coordinates, $W$, normalized ancilla, preparation identity and full ordinary
Petz action.

`forward_fidelity` and `reverse_fidelity` prove equality to the same common
fidelity at their respective different states. `result` quantifies over every
complex $U'$ with $U'U'^\dagger=I$ and $MU'\succeq0$ in each instance. The
prepared source rows define a CPTP decoder on every physical matrix and have
the stated strict comparison. No decoder action or fidelity reduction is a
premise.

## Triage

The settlement is proved for the two explicit witnesses: SW is strictly better
than ordinary Petz in the replacement instance, and strictly worse in the
reverse instance. Therefore neither decoder uniformly dominates the other on
the source domain. The conclusion applies to every complex positive-polar
completion covered by the theorem and leaves the physical support, source
environment and completion quantifiers intact.

Sun Woo P. Kim, *Optimal recovery for quantum error correction*,
arXiv:2603.06520v1, Proposition 3, Eqs. (20)–(22), and Corollary 4, preserves
the related CSS/Pauli posterior-sampling comparison. Raban Iten, Joseph M.
Renes and David Sutter, *Pretty good measures in quantum information theory*,
arXiv:1608.08229v2, Section 3.3 after Eq. (54), supplies the pretty-good
singlet-recovery commutator criterion. These are prior results, not discoveries
of this formalization.

The result does not settle Question 2, classify all channels, assert uniform
strict advantage, or claim that every input admits both directions.

## ASSUMED-UNVERIFIED

The bounded literature check did not authenticate the inaccessible publisher
article and did not constitute an exhaustive citation search. The new
source-owner four-slot registrations remain unfinished in
[issue #22675](https://github.com/the-omega-institute/trureturing/issues/22675);
no new `declared_validated` registration is claimed. Global novelty and claims
beyond the two kernel-certified instances remain unverified.
