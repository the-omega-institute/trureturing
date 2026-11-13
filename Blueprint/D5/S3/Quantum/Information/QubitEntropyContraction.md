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

At (1,0,0) the three entropy values are 0, ln(2) and ln(2). Changing the nonzero coordinate to -1 or permuting coordinates gives the same total. Thus the universal lower bound 2 ln(2) is sharp.

The equality cases follow from the existing private radial_concave lemma in QubitEntropyContraction. Set L=ln(2)>0 and f(u)=h((1+sqrt(u))/2) for u in [0,1]. This lemma supplies concavity of f, with f(0)=L and f(1)=0. Subtract the endpoint chord to define g(u)=f(u)-(1-u)L. Then g is concave, g(0)=g(1)=0, and g(u) is nonnegative throughout [0,1]. At the interior point u=1/4, sqrt(u)=1/2 and h(3/4)=2L-(3/4)ln(3), so $\operatorname{g}(\frac{1}{4})=\frac{5L-3\operatorname{ln}(3)}{4}=\frac{\operatorname{ln}(32)-\operatorname{ln}(27)}{4}> 0$. The logarithm identities ln(32)=5 ln(2) and ln(27)=3 ln(3), together with 0<27<32 and strict increase of the natural logarithm on positive numbers, give this strict sign.

For 0<u<=1/4, write u=(1-4u)0+(4u)(1/4). Both weights are nonnegative and sum to one. Concavity of g gives $\operatorname{g}(u)\ge 4u\,\operatorname{g}(\frac{1}{4})> 0$. For 1/4<u<1, write u=(4(1-u)/3)(1/4)+((4u-1)/3)1. Again the weights are nonnegative and sum to one, and concavity gives $\operatorname{g}(u)\ge \frac{4(1-u)}{3}\,\operatorname{g}(\frac{1}{4})> 0$. Hence g(u)>0 for every 0<u<1. This uses the existing concavity and one positive chord gap; no strict-concavity assertion or new derivative argument is needed.

For any real r in [-1,1], sqrt(r squared)=abs(r), and entropy symmetry identifies f(r squared) with h((1+r)/2) for both signs of r. Consequently the coordinate gap $\operatorname{h}(\frac{1+r}{2})-(1-r^{2})L=\operatorname{g}(r^{2})$ is nonnegative, is strictly positive when 0<r squared<1, and vanishes exactly when r squared is 0 or 1. The endpoint evaluations include r=0 and r=+1 or -1.

Write H=h((1+x)/2)+h((1+y)/2)+h((1+z)/2) and s=x squared+y squared+z squared. The preceding identities give the exact slack decomposition $H-2L=(1-s)L+\operatorname{g}(x^{2})+\operatorname{g}(y^{2})+\operatorname{g}(z^{2})$. Under the closed-ball hypothesis s<=1, all four terms on the right are nonnegative. Thus H=2L forces s=1, since L>0, and each coordinate gap must vanish. Each squared coordinate is therefore 0 or 1; their sum being one forces exactly one to be one and the other two to be zero. Conversely, each such triple has entropy values 0,L,L in some order, so H=2L.

For every real x,y,z with x squared+y squared+z squared<=1, the complete conclusion is H>=2 ln(2), with H=2 ln(2) if and only if (x squared=1 and y=z=0), or (y squared=1 and x=z=0), or (z squared=1 and x=y=0). Equivalently, the minimizers are exactly (1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1) and (0,0,-1). Every interior point has H>2 ln(2). This classification applies the existing scalar concavity and contraction results. Here h is Real.binEntropy on [0,1], with natural logarithms and zero endpoint terms. The conclusion concerns real coordinates; a physical Born-probability interpretation, a stronger uncertainty relation and a literature novelty claim are outside this derivation.

## References

- Truth anchor: `D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction`
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](QubitNormalFormState.md)
