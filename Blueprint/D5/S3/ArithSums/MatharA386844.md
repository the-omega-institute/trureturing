# Mathar's A386844 twin recurrence problem

## Abstract

The native A386844 binomial sum, both guarded signed recurrences, and ordinary formal D-finiteness.

The sequence is the inclusive natural binomial sum in OEIS A386844. The two recurrences are Mathar's conjectures in revision 16. Their starting indices 3 and 2 are the natural-lag interpretations: both endpoints are included. Every polynomial and signed recurrence operation is evaluated in the integers after casting n and a(n); only the lag indices use natural subtraction.

**Definition 1.1 (Literal native sequence).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right)=\sum_{k=0}^{n} \operatorname{choose}\left(3 \cdot n + 2, k\right) \cdot \operatorname{choose}\left(3 \cdot n - k, n - k\right)$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both k=0 and k=n are included, and n ranges over all natural numbers including zero. The values a(n) are natural numbers.

**Definition 1.2 (Third lag signed expression).**

$$\forall n:\mathbb{N}, R_{3}(n)=3 \cdot (n:\mathbb{Z}) \cdot \left(2 \cdot (n:\mathbb{Z}) - 1\right) \cdot (\operatorname{a}\left(n\right):\mathbb{Z}) + \left(0 - 353 \cdot (n:\mathbb{Z})^{2} + 1009 \cdot (n:\mathbb{Z}) - 672\right) \cdot (\operatorname{a}\left(n - 1\right):\mathbb{Z}) + \left(3938 \cdot (n:\mathbb{Z})^{2} - 15029 \cdot (n:\mathbb{Z}) + 13872\right) \cdot (\operatorname{a}\left(n - 2\right):\mathbb{Z}) - 399 \cdot \left(3 \cdot (n:\mathbb{Z}) - 4\right) \cdot \left(3 \cdot (n:\mathbb{Z}) - 5\right) \cdot (\operatorname{a}\left(n - 3\right):\mathbb{Z})$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.R3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is integer valued. The recurrence asserts its vanishing only for n>=3, including 3.

**Definition 1.3 (Second lag signed expression).**

$$\forall n:\mathbb{N}, R_{2}(n)=(n:\mathbb{Z}) \cdot \left(2 \cdot (n:\mathbb{Z}) - 1\right) \cdot \left(5 \cdot (n:\mathbb{Z}) - 8\right) \cdot (\operatorname{a}\left(n\right):\mathbb{Z}) + \left(0 - 145 \cdot (n:\mathbb{Z})^{3} + 362 \cdot (n:\mathbb{Z})^{2} - 264 \cdot (n:\mathbb{Z}) + 63\right) \cdot (\operatorname{a}\left(n - 1\right):\mathbb{Z}) + 3 \cdot \left(3 \cdot (n:\mathbb{Z}) - 1\right) \cdot \left(5 \cdot (n:\mathbb{Z}) - 3\right) \cdot \left(3 \cdot (n:\mathbb{Z}) - 2\right) \cdot (\operatorname{a}\left(n - 2\right):\mathbb{Z})$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.R2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is integer valued. The recurrence asserts its vanishing only for n>=2, including 2.

**Definition 1.4 (Complete ordinary series).**

$$A=\sum_{n=0}^{\infty} (\operatorname{a}\left(n\right):\mathbb{Q}) \cdot z^{n}$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A belongs to Q[[z]] and has rational coefficient a(n) at every natural index. It is an ordinary formal power series, with no convergence assumption.

**Definition 1.5 (Iterated formal derivative).**

$$\forall j:\mathbb{N}, \forall f:\mathbb{Q}[[z]], \operatorname{D}\left(j, f\right)=derivative^{j}(f)$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The superscript on derivative denotes function iteration. D(0,f)=f.

**Definition 1.6 (Finite polynomial differential operator).**

$$\forall r:\mathbb{N}, \forall p:\operatorname{Fin}\left(r + 1\right) \to \mathbb{Q}[z], \forall f:\mathbb{Q}[[z]], \operatorname{op}\left(r, p, f\right)=\sum_{j=0}^{r} \operatorname{p}\left(j\right) \cdot \operatorname{D}\left(j, f\right)$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.op` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum uses all finite indices j from zero through r. Each polynomial is embedded into Q[[z]] before multiplication.

**Definition 1.7 (Exact whole conjunction).**

$$P\iff (\forall n:\mathbb{N}, 3 \le n \implies R_{3}(n)=0) \land (\forall n:\mathbb{N}, 2 \le n \implies R_{2}(n)=0) \land (\exists r:\mathbb{N}, \exists p:\operatorname{Fin}\left(r + 1\right) \to \mathbb{Q}[z], (\exists j:\operatorname{Fin}\left(r + 1\right), \operatorname{p}\left(j\right) \neq 0) \land \operatorname{op}\left(r, p, A\right)=0)$$

*Formalization.* `D5/S3/ArithSums/MatharA386844.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P requires both universal signed recurrences and a finite nonzero homogeneous polynomial differential operator on this same complete A.

**Theorem 1.8 (Both recurrences and ordinary D-finiteness).**

$$(\forall n:\mathbb{N}, 3 \le n \implies R_{3}(n)=0) \land (\forall n:\mathbb{N}, 2 \le n \implies R_{2}(n)=0) \land (\exists r:\mathbb{N}, \exists p:\operatorname{Fin}\left(r + 1\right) \to \mathbb{Q}[z], (\exists j:\operatorname{Fin}\left(r + 1\right), \operatorname{p}\left(j\right) \neq 0) \land \operatorname{op}\left(r, p, A\right)=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/MatharA386844.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal coefficient identity identifies A with (1+w)^3/(1-5w), where w has zero constant term and z(1+w)^3=w(1-w)^2. Lagrange substitution supplies this all-index bridge. The transported numerator identities give O3 A=8z+532z^2 and O2 A=-8z. Coefficient extraction gives the stated guarded recurrences, including their endpoints. Applying theta-1 to the second forcing identity and cancelling z^2 gives the ordinary differential operator with coefficients 420; 3612z-177; 4593z^2-1209z+6; 1539z^3-943z^2+29z; 135z^4-145z^3+10z^2. Its constant coefficient polynomial 420 is nonzero. All substitutions and derivatives are formal.

## References

- Truth anchor: `D5/S3/ArithSums/MatharA386844.A`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.D`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.P`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.R2`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.R3`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.a`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.op`
- Truth anchor: `D5/S3/ArithSums/MatharA386844.result`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../../S1/Recurrence/A308815DFiniteRecurrence.md)
- Dependency: [D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix](../Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.md)
