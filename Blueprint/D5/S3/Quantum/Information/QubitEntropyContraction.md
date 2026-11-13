# QubitEntropyContraction

## Abstract

Quadratic contraction for an actual symmetric qubit ensemble

**Theorem 1.1 (Quadratic contraction for an actual symmetric qubit ensemble).**

$$\forall x,z,t:\mathbb{R},\ {(x^{2})+(z^{2})\le 1\land 0\le t\land t\le 1}\implies 0\le \operatorname{qubitHolevo}(x, (t)\times (z))\land \operatorname{qubitHolevo}(x, (t)\times (z))\le (t^{2})\times (\operatorname{qubitHolevo}(x, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases.

An application to three real coordinates uses binary entropy in nats. For p in the closed unit interval, write $\operatorname{h}(p)=-p\,\operatorname{ln}(p)-(1-p)\,\operatorname{ln}(1-p)$. Each zero-times-log-zero endpoint term is defined as zero, and all logarithms are natural.

For any real r in [-1,1], specialize qubit_holevo_contraction with its parameters x=0, z=1 and t=abs(r). The disk hypothesis holds at (0,1), and abs(r) lies in [0,1]. Unfolding QubitNormalFormState.qubitHolevo and QubitNormalFormState.qubit_state_entropy identifies the scaled Holevo entropy with ln(2) minus h((1+abs(r))/2), while the unscaled value is ln(2). The identity sqrt(r squared)=abs(r) and binary-entropy symmetry h(p)=h(1-p) remove the absolute value; h(1/2)=ln(2) and h(1)=0 evaluate the endpoints. The contraction therefore gives $\operatorname{ln}(2)-\operatorname{h}(\frac{1+r}{2})\le r^{2}\,\operatorname{ln}(2)$. This includes both signs and the endpoint coordinates.

Now let x, y and z be real numbers in the closed unit ball, so their squared coordinates sum to at most one. Each coordinate is in [-1,1]. Applying the preceding bound to each coordinate and adding yields $\operatorname{h}(\frac{1+x}{2})+\operatorname{h}(\frac{1+y}{2})+\operatorname{h}(\frac{1+z}{2})\ge (3-(x^{2}+y^{2}+z^{2}))\,\operatorname{ln}(2)\ge 2\,\operatorname{ln}(2)$. The last step uses nonnegativity of ln(2), so the conclusion covers the entire closed ball, including its interior and boundary.

At (1,0,0) the three entropy values are 0, ln(2) and ln(2). Changing the nonzero coordinate to -1 or permuting coordinates gives the same total. Thus the universal lower bound 2 ln(2) is sharp. These examples do not classify all equality cases. This is an application of the existing contraction theorem; a physical Born-probability interpretation, a stronger uncertainty relation and a literature novelty claim are outside this derivation.

## References

- Truth anchor: `D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction`
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](QubitNormalFormState.md)
