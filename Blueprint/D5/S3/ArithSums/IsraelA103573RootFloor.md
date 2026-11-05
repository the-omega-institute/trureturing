# Israel's A103573 ceiling formula

## Abstract

Least integer thresholds for the difference of a square root and a cube root.

**Definition 1.1 (The root difference).**

$$\forall x \in \mathrm{Real},\; \operatorname{f}\left(x\right) = \operatorname{sqrt}\left(x\right) - x^{\frac{1}{3}}$$

*Formalization.* `D5/S3/ArithSums/IsraelA103573RootFloor.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ray G. Opao; Robert Israel (2026). *OEIS A103573, least integer root-difference thresholds*. URL: <https://oeis.org/A103573/internal>.

*Commentary.*

For a nonnegative real argument, sqrt is the nonnegative square root and the real power with exponent 1/3 is the nonnegative cube root.

**Definition 1.2 (The explicit approximation).**

$$\forall n \in \mathrm{Nat},\; \operatorname{T}\left(n\right) = (n : \mathrm{Real})^{2} + 2 \cdot (n : \mathrm{Real})^{\frac{5}{3}} + \frac{7}{3} \cdot (n : \mathrm{Real})^{\frac{4}{3}} + 2 \cdot (n : \mathrm{Real}) + \frac{110}{81} \cdot (n : \mathrm{Real})^{\frac{2}{3}} + \frac{182}{243} \cdot (n : \mathrm{Real})^{\frac{1}{3}}$$

*Formalization.* `D5/S3/ArithSums/IsraelA103573RootFloor.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ray G. Opao; Robert Israel (2026). *OEIS A103573, least integer root-difference thresholds*. URL: <https://oeis.org/A103573/internal>.

*Commentary.*

All rational coefficients and exponents are real. The approximation is zero at n=0.

**Definition 1.3 (The source sequence).**

$$\forall a \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(a\right) \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; \operatorname{IsLeast}\left(\{k : \mathrm{Nat} \mid \lfloor \operatorname{f}\left((k : \mathrm{Real})\right) \rfloor = (n : \mathrm{Int})\}, a\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/IsraelA103573RootFloor.IsSourceSequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ray G. Opao; Robert Israel (2026). *OEIS A103573, least integer root-difference thresholds*. URL: <https://oeis.org/A103573/internal>.

*Commentary.*

At every natural index n, the sequence takes the least natural k whose ordinary integer floor of sqrt(k)-k^(1/3) is n. The floor is integer valued even when its argument is negative.

**Definition 1.4 (The full ceiling assertion).**

$$claim \Leftrightarrow \left(\left(\exists a \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(a\right)\right) \land \left(\forall a \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(a\right) \Rightarrow \left(\forall n \in \mathrm{Nat},\; (a\left(n\right) : \mathrm{Int}) = \operatorname{ceil}\left(\operatorname{T}\left(n\right)\right) \lor (a\left(n\right) : \mathrm{Int}) = \operatorname{ceil}\left(\operatorname{T}\left(n\right)\right) + 1\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/IsraelA103573RootFloor.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ray G. Opao; Robert Israel (2026). *OEIS A103573, least integer root-difference thresholds*. URL: <https://oeis.org/A103573/internal>.

*Commentary.*

The assertion includes existence of the source sequence and applies to every sequence satisfying its leastness definition, at every index including zero.

**Theorem 1.5 (Two consecutive ceiling values).**

$$\left(\exists a \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(a\right)\right) \land \left(\forall a \in (\mathrm{Nat} \to \mathrm{Nat}),\; \operatorname{IsSourceSequence}\left(a\right) \Rightarrow \left(\forall n \in \mathrm{Nat},\; (a\left(n\right) : \mathrm{Int}) = \operatorname{ceil}\left(\operatorname{T}\left(n\right)\right) \lor (a\left(n\right) : \mathrm{Int}) = \operatorname{ceil}\left(\operatorname{T}\left(n\right)\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/IsraelA103573RootFloor.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ray G. Opao; Robert Israel (2026). *OEIS A103573, least integer root-difference thresholds*. URL: <https://oeis.org/A103573/internal>.

*Commentary.*

For n>0 the polynomial q(t)=t^3-t^2 increases strictly on t>=1 and supplies a threshold r with sqrt(r)-r^(1/3)=n. Put y=n^(1/3) and P_n(X)=X*(X+3*n^2)^2-((3*n+1)*X+n^3)^2. Exact polynomial expansion gives P_n(T(n))<0<P_n(T(n)+1), since the residual factors have positive coefficients. The discarded factor in the square comparison is positive, so these signs imply T(n)<r<T(n)+1. The least admissible integer is ceil(r): its root difference lies in [n,n+1), and all smaller nonnegative integers have root difference below n. Ceiling monotonicity leaves the two stated integer possibilities. At n=0 the least candidate and the approximation are both zero.

## References

- Truth anchor: `D5/S3/ArithSums/IsraelA103573RootFloor.IsSourceSequence`
- Truth anchor: `D5/S3/ArithSums/IsraelA103573RootFloor.T`
- Truth anchor: `D5/S3/ArithSums/IsraelA103573RootFloor.claim`
- Truth anchor: `D5/S3/ArithSums/IsraelA103573RootFloor.f`
- Truth anchor: `D5/S3/ArithSums/IsraelA103573RootFloor.result`
