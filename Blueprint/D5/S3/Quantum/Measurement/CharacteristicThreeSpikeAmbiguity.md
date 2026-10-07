# Characteristic-three flat-plus-spike ambiguity

## Abstract

Flat-plus-spike states have uniformly nonvanishing characteristic-three ambiguity.

Let K be any finite field with a decidable equality, q its cardinality, s=sqrt(q), and N=2q+2s. The complex additive character psi is arbitrary. All sums run over K. This is an ambiguity calculation on field labels; no cyclic displacement or projector-Gram spectral identity is assumed.

**Definition 1.1 (The flat vector plus a spike).**

$$\phi(x)=\frac{1+s\operatorname{indicatorZero}(x)}{\sqrt{N}}$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every x in K, spikeState K x is (1+s if x=0, otherwise 1)/sqrt(N). It equals (|+_q>+|0>)/sqrt(2+2/s), the phase-zero specialization of Zhu–Wang equation (62). That equation is stated for characteristic two in the paper; the characteristic-three bounds below are derived here.

**Definition 1.2 (The finite-character ambiguity coefficient).**

$$\operatorname{ambiguity}(psi,f,a,b)=\sum_{x:K}\overline{\operatorname{f}(x)}\operatorname{psi}(b(x-a))\operatorname{f}(x-a)$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.ambiguity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every psi : AddChar K C, f : K -> C and a,b in K, ambiguity is the displayed finite sum. This is <f,X_a Z_b f> with X_a f(x)=f(x-a) and Z_b f(x)=psi(bx)f(x). Star is complex conjugation.

**Theorem 1.3 (Coordinate normalization).**

$$\sum_{x:K}\Vert \phi(x) \Vert^{2}=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every finite field K, with no character or characteristic restriction, the squared coordinate moduli of spikeState sum to one. The unnormalized mass is q+2s+s^2=2q+2s.

**Theorem 1.4 (The exact overlap).**

$$A(a,b)=\frac{q\operatorname{indicatorZero}(b)+q\operatorname{indicatorZero}(a)+s(1+\operatorname{psi}(-ba))}{N}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every finite field K, nontrivial psi (psi != 1 as an additive character), and all a,b in K, A(a,b)=ambiguity psi (spikeState K) a b has this value. Indicator(t) means 1 when t=0 and 0 otherwise. The character sum uses Mathlib's sum_mulShift and IsPrimitive.of_ne_one. The sign -ba follows from the field X_a Z_b convention.

**Theorem 1.5 (Nonidentity intensity floor).**

$$\frac{1}{4(s+1)^{2}}\le\Vert A(a,b) \Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_intensity_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every finite field K of characteristic three, every nontrivial psi, and every a,b with a!=0 or b!=0, the displayed bound holds. Off the axes psi(-ba)^3=1 implies |1+psi(-ba)|^2>=1. On an axis the numerator is q+2s, which also meets the lower bound. No Gram matrix or eigenvalue is defined by this theorem.

**Theorem 1.6 (Uniform ambiguity-side SIC scale).**

$$\sum_{x:K}\Vert \phi(x) \Vert^{2}=1\land\frac{1}{8}\le(q+1)\Vert A(a,b) \Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_uniform_ambiguity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiuwu Zhu; Yu Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

For every finite field K of characteristic three, every nontrivial psi, and every nonidentity label, the vector is normalized and (q+1)|A(a,b)|^2>=1/8. The dimension-independent constant follows from (s-1)^2>=0. This bounds normalized ambiguity intensities, not an assumed spectrum.

The formalized Gram/Rayleigh interface remains open: the target is one unit vector on each F_(3^r), for every integer r>=1, with one c>0 such that Re(w*G^Pi w) >= c q/(q+1) sum |w|^2 whenever sum w=0. A canonical trace-character instantiation and a proved finite-field Weyl/Fourier Gram identity are still required to use c=1/8. This module proves neither the target family Rayleigh bound nor POVM completeness.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.ambiguity`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_ambiguity`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_intensity_lower_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_normalized`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_uniform_ambiguity_bound`
