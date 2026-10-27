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

Laura Burri, *Entanglement fidelity of Petz decoder for one-shot entanglement
transmission*, arXiv:2502.17411v1, Section 3.3, Question 1:

> Which performs better: the SW decoder or the Petz decoder?

The source domain is every density state and CPTP noise channel (Section 3.1,
Theorem 1). The question concerns the actual Appendix A SW decoder and ordinary
Petz decoder, measured by canonical entanglement fidelity. It is separate from
Question 2's comparison with a lower bound.

## Mathematical answer and parameter correspondence

The [owning Scribe](../Blueprint/D5/S3/Quantum/Recovery/BurriDecoderComparison.scribe.cs)
contains the full instance data and cites the physical construction proofs.
The common root vector is $v(r,i)=(\sqrt\rho)_{i,r}$, in reference-first order;
its pure density is normalized and has channel-input marginal $\rho$.
The actual channel acts on each reference-indexed block. Its overlap with
the same pure density is the squared-fidelity convention of the source.

For the first instance, $A=\mathrm{Fin}\,2$, $B=\mathrm{Fin}\,1$,
$E=A\times B$ and $\rho=\operatorname{diag}(2/3,1/3)$.
The isometry sends $|i\rangle$ to $|0\rangle_B|i,0\rangle_E$.
The normalized correlated root vector also supplies the fixed ancilla;
$W=I$. The source matrix is the literal transposed root product.
SW has fidelity $11/27$, ordinary Petz has fidelity $1/3$, and their gap is
$2/27$. This uses the existing `BurriReplacementDecoder` source, including
its full-channel Petz identification and supported-action uniqueness.

For the second instance, $A=\mathrm{Fin}\,2$,
$B=\mathrm{Fin}\,2\times\mathrm{Fin}\,3$, $E=A\times B$,
$\rho=I_2/2$. The Scribe specifies the positive $6\times6$ matrix $Y$ and
physical Kraus operators $K_a(b,i)=Y((i,a),b)/\sqrt{31}$, retaining the full
twelve-dimensional environment. The output is $Y^2/62$.
Ordinary Petz has fidelity $27/31$; the actual SW fidelity is strictly smaller
by an exact radical sum-of-squares certificate. The seven `BurriReverse*`
modules prove the isometry, state, marginals, positive roots, literal source
matrix, full SVD with eighteen null coordinates, $W$, normalized ancilla,
preparation identity and full ordinary Petz action.

`forward_fidelity` and `reverse_fidelity` prove equality to the same common
fidelity, at their respective different states. The reverse equality uses an
actual tensor-order reindexing of the vector, density and channel extension.
`result` quantifies over every complex $U'$ with $U'U'^\dagger=I$ and
$MU'\succeq0$ in each instance. The prepared source rows define a CPTP decoder
on every physical matrix and have the stated strict comparison. No decoder
action or fidelity reduction is a premise. Hence neither decoder uniformly
dominates the other on the source domain.

## Standing and acceptance boundary

The [literature entry](../Library/Quantum/burri2025petztransmission.md) preserves
Kim's CSS/Pauli sampling comparison and the Iten–Renes–Sutter pretty-good
optimality criterion, with exact version and section locators. The bounded
checked primary sources do not establish an unrestricted two-instance
comparison. This is neither a global priority certificate nor a claim that
the forward direction was previously unknown.

The result supplies two opposite strict witnesses. It does not settle
Question 2, classify all channels, or assert that every input admits both
directions. Scoped Lean and Scribe evidence supports independent review;
formal freezing and repository acceptance remain separate steps.

The new source-owner four-slot registrations remain unfinished in
[issue #22675](https://github.com/the-omega-institute/trureturing/issues/22675).
No new `declared_validated` registration is claimed.
