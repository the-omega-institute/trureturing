# Golden Norm Charts and the Exact Stationary Phase

## Abstract

An invertible golden norm chart retains the quadratic normal phase at odd precision.

The carrier is the existing GoldenApparition.GoldenMod M. Coordinates and coefficients belong to ZMod M, even when M is composite. No field instance is imposed on that ring. The inverse certificates 2*half=1 and normForm(z)*invc=1 are explicit hypotheses.

**Definition 1.1 (Actual modular golden norm).**

$$\forall z \in \operatorname{GoldenMod}\left(M\right), \operatorname{normForm}\left(z\right) = \operatorname{a}\left(z\right)^{2} + \operatorname{a}\left(z\right) \cdot \operatorname{b}\left(z\right) - \operatorname{b}\left(z\right)^{2}$$

*Formalization.* `D5/S3/Arith/GoldenConicStationaryChart.normForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normForm(z)=z.a^2+z.a*z.b-z.b^2, the reduction of the original integer golden norm in its existing coordinate basis.

**Definition 1.2 (The specified tangent direction).**

$$\forall z \in \operatorname{GoldenMod}\left(M\right), \operatorname{tangent}\left(z\right) = \operatorname{GoldenModMk}\left(\operatorname{a}\left(z\right) - 2 \cdot \operatorname{b}\left(z\right), \operatorname{neg}\left(2 \cdot \operatorname{a}\left(z\right) + \operatorname{b}\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicStationaryChart.tangent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tangent is (z.a-2*z.b,-2*z.a-z.b). It is orthogonal to the norm gradient and has norm -5*normForm(z).

**Definition 1.3 (The chart with a certified inverse).**

$$\forall z \in \operatorname{GoldenMod}\left(M\right), \forall t \in \operatorname{ZMod}\left(M\right), \forall d \in \operatorname{ZMod}\left(M\right), \operatorname{chart}\left(z, t, d\right) = \operatorname{GoldenModMk}\left(d \cdot \left(\left(1 + 5 \cdot t^{2}\right) \cdot \operatorname{a}\left(z\right) + 2 \cdot t \cdot \operatorname{a}\left(\operatorname{tangent}\left(z\right)\right)\right), d \cdot \left(\left(1 + 5 \cdot t^{2}\right) \cdot \operatorname{b}\left(z\right) + 2 \cdot t \cdot \operatorname{b}\left(\operatorname{tangent}\left(z\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicStationaryChart.chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

chart(z,t,d)=d*((1+5*t^2)*z+2*t*tangent(z)) coordinatewise. The theorem requires d*(1-5*t^2)=1 when invoking this inverse. No division by a nonunit is performed.

**Definition 1.4 (Radial coordinate in the moving basis).**

$$\forall z \in \operatorname{GoldenMod}\left(M\right), \forall w \in \operatorname{GoldenMod}\left(M\right), \forall half \in \operatorname{ZMod}\left(M\right), \forall invc \in \operatorname{ZMod}\left(M\right), \operatorname{radial}\left(z, w, half, invc\right) = half \cdot invc \cdot \left(\left(2 \cdot \operatorname{a}\left(z\right) + \operatorname{b}\left(z\right)\right) \cdot \operatorname{a}\left(w\right) + \left(\operatorname{a}\left(z\right) - 2 \cdot \operatorname{b}\left(z\right)\right) \cdot \operatorname{b}\left(w\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicStationaryChart.radial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With the stated inverse certificates, radial is the coefficient A of z when w=A*z+B*tangent(z).

**Definition 1.5 (Tangential coordinate in the moving basis).**

$$\forall z \in \operatorname{GoldenMod}\left(M\right), \forall w \in \operatorname{GoldenMod}\left(M\right), \forall half \in \operatorname{ZMod}\left(M\right), \forall invc \in \operatorname{ZMod}\left(M\right), \operatorname{transverse}\left(z, w, half, invc\right) = half \cdot invc \cdot \left(\operatorname{b}\left(z\right) \cdot \operatorname{a}\left(w\right) - \operatorname{a}\left(z\right) \cdot \operatorname{b}\left(w\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenConicStationaryChart.transverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

transverse is the coefficient B in the same moving basis. Its determinant denominator is the certified unit 2*normForm(z).

**Theorem 1.6 (Norm, unique inverse, and quadratic phase).**

$$\forall M \in \mathbb{N}, \forall z \in \operatorname{GoldenMod}\left(M\right), \forall half \in \operatorname{ZMod}\left(M\right), \forall invc \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(\operatorname{And}\left(2 \cdot half = 1, \operatorname{normForm}\left(z\right) \cdot invc = 1\right), \operatorname{And}\left(\forall t \in \operatorname{ZMod}\left(M\right), \forall d \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(d \cdot \left(1 - 5 \cdot t^{2}\right) = 1, \operatorname{And}\left(\operatorname{normForm}\left(\operatorname{chart}\left(z, t, d\right)\right) = \operatorname{normForm}\left(z\right), \forall lam \in \operatorname{ZMod}\left(M\right), lam \cdot \left(2 \cdot \operatorname{a}\left(z\right) + \operatorname{b}\left(z\right)\right) \cdot \operatorname{a}\left(\operatorname{chart}\left(z, t, d\right)\right) + lam \cdot \left(\operatorname{a}\left(z\right) - 2 \cdot \operatorname{b}\left(z\right)\right) \cdot \operatorname{b}\left(\operatorname{chart}\left(z, t, d\right)\right) = 2 \cdot lam \cdot \operatorname{normForm}\left(z\right) + 20 \cdot lam \cdot \operatorname{normForm}\left(z\right) \cdot t^{2} \cdot d\right)\right), \operatorname{And}\left(\forall w \in \operatorname{GoldenMod}\left(M\right), \operatorname{Implies}\left(\operatorname{normForm}\left(w\right) = \operatorname{normForm}\left(z\right), \forall e \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(e \cdot \left(1 + \operatorname{radial}\left(z, w, half, invc\right)\right) = 1, \operatorname{And}\left(\left(1 + \operatorname{radial}\left(z, w, half, invc\right)\right) \cdot half \cdot \left(1 - 5 \cdot \left(\operatorname{transverse}\left(z, w, half, invc\right) \cdot e\right)^{2}\right) = 1, \operatorname{And}\left(\operatorname{chart}\left(z, \operatorname{transverse}\left(z, w, half, invc\right) \cdot e, \left(1 + \operatorname{radial}\left(z, w, half, invc\right)\right) \cdot half\right) = w, \forall t \in \operatorname{ZMod}\left(M\right), \forall d \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(d \cdot \left(1 - 5 \cdot t^{2}\right) = 1, \operatorname{Implies}\left(\operatorname{chart}\left(z, t, d\right) = w, t = \operatorname{transverse}\left(z, w, half, invc\right) \cdot e\right)\right)\right)\right)\right)\right), \forall t \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(t^{3} = 0, \operatorname{And}\left(\operatorname{chart}\left(z, t, 1 + 5 \cdot t^{2}\right) = \operatorname{GoldenModMk}\left(\left(1 + 10 \cdot t^{2}\right) \cdot \operatorname{a}\left(z\right) + 2 \cdot t \cdot \operatorname{a}\left(\operatorname{tangent}\left(z\right)\right), \left(1 + 10 \cdot t^{2}\right) \cdot \operatorname{b}\left(z\right) + 2 \cdot t \cdot \operatorname{b}\left(\operatorname{tangent}\left(z\right)\right)\right), \operatorname{And}\left(\operatorname{normForm}\left(\operatorname{chart}\left(z, t, 1 + 5 \cdot t^{2}\right)\right) = \operatorname{normForm}\left(z\right), \forall lam \in \operatorname{ZMod}\left(M\right), lam \cdot \left(2 \cdot \operatorname{a}\left(z\right) + \operatorname{b}\left(z\right)\right) \cdot \operatorname{a}\left(\operatorname{chart}\left(z, t, 1 + 5 \cdot t^{2}\right)\right) + lam \cdot \left(\operatorname{a}\left(z\right) - 2 \cdot \operatorname{b}\left(z\right)\right) \cdot \operatorname{b}\left(\operatorname{chart}\left(z, t, 1 + 5 \cdot t^{2}\right)\right) = 2 \cdot lam \cdot \operatorname{normForm}\left(z\right) + 20 \cdot lam \cdot \operatorname{normForm}\left(z\right) \cdot t^{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenConicStationaryChart.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every modulus M and unit-norm point z with the two inverse certificates, every valid chart point has exactly the original norm. A normal frequency lambda*gradient(Q)(z) has phase 2*lambda*Q(z)+20*lambda*Q(z)*t^2*d.

Conversely, for every w with the same norm, put A=radial(z,w,half,invc) and B=transverse(z,w,half,invc). If e*(1+A)=1, the explicitly recovered parameter B*e and denominator inverse (1+A)*half give w. Any other chart representation has that same parameter. In a ball modulo p^h about z, A is one and B is zero modulo p^h, so this inverse covers the entire ball when p is odd.

If t^3=0, the exact point is (1+10*t^2)*z+2*t*tangent(z), and its normal phase is 2*lambda*Q(z)+20*lambda*Q(z)*t^2. At modulus p^(2*r+1), a parameter divisible by p^r has cube zero for r>=1, while its square can remain nonzero. This is the quadratic term in the odd-precision Gauss sum.

The proof constructs the basis inverse, derives A^2-5*B^2=1 from the actual norm, and verifies the inverse and phase by ring identities. The analytic character-sum evaluation is treated separately in the existing theory note and lies outside this theorem.

## References

- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.chart`
- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.normForm`
- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.radial`
- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.result`
- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.tangent`
- Truth anchor: `D5/S3/Arith/GoldenConicStationaryChart.transverse`
