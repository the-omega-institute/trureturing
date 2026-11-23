# Bare finite Drazin equalities

## Abstract

Three tests characterize the bare Drazin sum equality in a unital associative ring.

**Definition 1.1 (The finite Drazin relation).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (x,y: R), \operatorname{FD}\left(x, y\right) \iff (yxy = y \land xy = yx \land \operatorname{IsNilpotent}\left(x - xyx\right))$$

*Formalization.* `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.FD` (`✓ std3`).

*Citation.* Yaashaa Golovanov (2026). *Spectral coincidence and generalized Hua inversion in rings and Banach algebras*. DOI: [10.48550/arXiv.2611.19664](https://doi.org/10.48550/arXiv.2611.19664). URL: <https://arxiv.org/pdf/2611.19664v1#page=29>.

*Commentary.*

The finite Drazin relation requires an outer inverse, commutation with the input, and nilpotence of the remainder. Nilpotence means that some natural power is zero.

**Definition 1.2 (The finite Drazin inverse).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (x: R) (h_{x}: \exists (y: R), \operatorname{FD}\left(x, y\right)), \operatorname{drazin}\left(x, h_{x}\right) = x^{D}$$

*Formalization.* `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.drazin` (`✓ std3`).

*Citation.* Yaashaa Golovanov (2026). *Spectral coincidence and generalized Hua inversion in rings and Banach algebras*. DOI: [10.48550/arXiv.2611.19664](https://doi.org/10.48550/arXiv.2611.19664). URL: <https://arxiv.org/pdf/2611.19664v1#page=29>.

*Commentary.*

An existence proof supplies a finite Drazin witness. Any two witnesses coincide. A common positive power absorbs both core idempotents and can be multiplied by the same powers of the candidate inverses to identify the cores and then the inverses.

**Theorem 1.3 (Golovanov's Problem 10.1).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (a,c,u,v,b: R), (a+c)b = 1 \to b(a+c) = 1 \to \operatorname{FD}\left(a, u\right) \to \operatorname{FD}\left(c, v\right) \to \operatorname{let} p := au, \operatorname{let} r := cv, \operatorname{let} z := r - p, \operatorname{let} n_{a} := a - pa, \operatorname{let} n_{c} := c - rc, \operatorname{let} t := a - aba, \operatorname{let} P := cbn_{a}bc + abn_{c}ba, (\exists (h_{t}: \exists (y: R), \operatorname{FD}\left(t, y\right)), t^{D} = a^{D} + c^{D}) \iff (abz = zba \land zbz = 0 \land \operatorname{IsNilpotent}\left(P\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yaashaa Golovanov (2026). *Spectral coincidence and generalized Hua inversion in rings and Banach algebras*. DOI: [10.48550/arXiv.2611.19664](https://doi.org/10.48550/arXiv.2611.19664). URL: <https://arxiv.org/pdf/2611.19664v1#page=29>.

*Commentary.*

The two unit equations identify b as the inverse of a + c. The input witnesses u and v are the finite Drazin inverses of a and c. The equivalence applies to every unital associative ring, including the zero ring, and allows different input core idempotents.

Put s = u + v. The ordered products a b c and c b a give ts = p + a b z and st = p + z b a, respectively.

The outer inverse defect sts − s equals the negative of zbz. The remainder t − (ts)t equals P by multiplying the two complementary core terms of 1 − ts by the appropriate ordered expression for t. These identities translate commutation, the outer inverse equation, and nilpotence into the three tests.

## References

- Truth anchor: `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.FD`
- Truth anchor: `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.drazin`
- Truth anchor: `D5/S3/ArithUnits/GolovanovBareDrazinEqualities.result`
