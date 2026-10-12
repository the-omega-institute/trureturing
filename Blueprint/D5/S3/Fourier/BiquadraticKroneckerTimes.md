# Biquadratic independence and integer approximation times

## Abstract

Two independent nonsquare classes over the rationals force four-coefficient independence of real quadratic roots; an integer-character condition gives approximation sequences on every finite torus.

**Theorem 1.1 (Four rational coefficients vanish).**

$$\forall p \in \mathbb{Q},\; \forall q \in \mathbb{Q},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; (x^{2} = (p:\mathbb{R}) \land \left(y^{2} = (q:\mathbb{R}) \land \left(\operatorname{Irrational}\left(x\right) \land \left(\left(\neg \operatorname{IsSquare}\left(q\right)\right) \land \left(\neg \operatorname{IsSquare}\left(p \cdot q\right)\right)\right)\right)\right)) \Rightarrow (\forall a \in \mathbb{Q},\; \forall b \in \mathbb{Q},\; \forall c \in \mathbb{Q},\; \forall d \in \mathbb{Q},\; ((a:\mathbb{R}) + (b:\mathbb{R}) \cdot x + (c:\mathbb{R}) \cdot y + (d:\mathbb{R}) \cdot (x \cdot y) = 0) \Rightarrow (a = 0 \land \left(b = 0 \land \left(c = 0 \land d = 0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/BiquadraticKroneckerTimes.biquadratic_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume x squared is p, y squared is q, x is irrational, and neither q nor pq is a rational square. Squaring the relation and separating the rational and x coefficients gives two equations. Their product eliminates the coefficient of xy through the nonsquare obstructions. The remaining coefficients then vanish. All rational coefficients and radicands are explicitly cast to the reals where necessary.

**Theorem 1.2 (Every torus target is approached).**

$$\forall I \in Type,\; [\operatorname{Fintype}\left(I\right)] \forall a \in I \to \mathbb{R},\; (\forall k \in I \to \mathbb{Z},\; \forall m \in \mathbb{Z},\; (\sum_{i \in I} (\operatorname{k}\left(i\right):\mathbb{R}) \cdot \operatorname{a}\left(i\right) = (m:\mathbb{R})) \Rightarrow (\forall i \in I,\; \operatorname{k}\left(i\right) = 0)) \Rightarrow (\forall z \in I \to Circle,\; \exists m \in \mathbb{N} \to \mathbb{N},\; \operatorname{Tendsto}\left((n:\mathbb{N} \mapsto (i:I \mapsto \operatorname{Circle}.\operatorname{exp}\left(2 \cdot \operatorname{Real}.\operatorname{pi} \cdot \operatorname{a}\left(i\right)\right)^{\operatorname{m}\left(n\right)})), atTop, \operatorname{nhds}\left(z\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/BiquadraticKroneckerTimes.dense_circle_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The character criterion TorusOrbitClosure.result identifies the closure of nonnegative powers. The assumption says that any integer combination of the frequencies which is an integer has all coefficients zero; equivalently the frequencies together with one have no nontrivial integer relation. The sequential characterization of closure then supplies natural exponents tending to the prescribed target. The exponents need not be monotone or unbounded, and no algebraicity assumption is imposed.

## References

- Truth anchor: `D5/S3/Fourier/BiquadraticKroneckerTimes.biquadratic_independent`
- Truth anchor: `D5/S3/Fourier/BiquadraticKroneckerTimes.dense_circle_sequence`
- Dependency: [D5/S3/Fourier/TorusOrbitClosure](TorusOrbitClosure.md)
