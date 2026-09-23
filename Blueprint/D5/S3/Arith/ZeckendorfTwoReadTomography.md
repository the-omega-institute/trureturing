# Two-Read Tomography of Zeckendorf Probability States

## Abstract

Two correlated cumulative-residue tests recover each mass on the arithmetic future quotient.

The coefficient ring is ZMod M with M positive, including composite moduli. Every indexed weight row has an explicit Bezout certificate. Distinct chosen projective representatives have nonzero determinant; the determinant is not assumed to be a unit.

**Definition 1.1 (First cumulative residue).**

$$\forall r \in \operatorname{ZMod}\left(M\right), \forall e \in \operatorname{ZMod}\left(M\right), \forall f \in \operatorname{ZMod}\left(M\right), \forall rp \in \operatorname{ZMod}\left(M\right), \forall up \in \operatorname{ZMod}\left(M\right), \forall vp \in \operatorname{ZMod}\left(M\right), \operatorname{firstResidual}\left(r, e, f, rp, up, vp\right) = rp - r \cdot \left(e \cdot up + f \cdot vp\right)$$

*Formalization.* `D5/S3/Arith/ZeckendorfTwoReadTomography.firstResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

To target residue r, use the coefficient pair (-r*e,-r*f). At candidate residue rp and row (up,vp), the resulting residue is rp-r*(e*up+f*vp). The earlier guarded-word construction realizes this pair with a legal word and returns the weight clock.

**Definition 1.2 (Second cumulative residue without reset).**

$$\forall r \in \operatorname{ZMod}\left(M\right), \forall u \in \operatorname{ZMod}\left(M\right), \forall v \in \operatorname{ZMod}\left(M\right), \forall e \in \operatorname{ZMod}\left(M\right), \forall f \in \operatorname{ZMod}\left(M\right), \forall rp \in \operatorname{ZMod}\left(M\right), \forall up \in \operatorname{ZMod}\left(M\right), \forall vp \in \operatorname{ZMod}\left(M\right), \operatorname{secondResidual}\left(r, u, v, e, f, rp, up, vp\right) = \operatorname{firstResidual}\left(r, e, f, rp, up, vp\right) + v \cdot up - u \cdot vp$$

*Formalization.* `D5/S3/Arith/ZeckendorfTwoReadTomography.secondResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The next coefficient pair is (v,-u), formed from the target row. Its contribution v*up-u*vp is added to the first residue. The first reading does not erase the accumulator or prepare a new state.

**Theorem 1.3 (Explicit separation and exact finite-mass recovery).**

$$\forall M \in \mathbb{N}, \operatorname{Implies}\left(\operatorname{NeZero}\left(M\right), \forall I \in \operatorname{Type}\left(\right), \operatorname{Implies}\left(\operatorname{Fintype}\left(I\right), \forall U \in \operatorname{Function}\left(I, \operatorname{ZMod}\left(M\right)\right), \forall V \in \operatorname{Function}\left(I, \operatorname{ZMod}\left(M\right)\right), \forall E \in \operatorname{Function}\left(I, \operatorname{ZMod}\left(M\right)\right), \forall F \in \operatorname{Function}\left(I, \operatorname{ZMod}\left(M\right)\right), \forall d \in I, \forall r \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(\operatorname{And}\left(\forall i \in I, \operatorname{E}\left(i\right) \cdot \operatorname{U}\left(i\right) + \operatorname{F}\left(i\right) \cdot \operatorname{V}\left(i\right) = 1, \forall i \in I, \forall j \in I, \operatorname{Implies}\left(\operatorname{Not}\left(i = j\right), \operatorname{Not}\left(\operatorname{V}\left(i\right) \cdot \operatorname{U}\left(j\right) - \operatorname{U}\left(i\right) \cdot \operatorname{V}\left(j\right) = 0\right)\right)\right), \operatorname{And}\left(\forall rp \in \operatorname{ZMod}\left(M\right), \forall up \in \operatorname{ZMod}\left(M\right), \forall vp \in \operatorname{ZMod}\left(M\right), \forall ep \in \operatorname{ZMod}\left(M\right), \forall fp \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(ep \cdot up + fp \cdot vp = 1, \operatorname{Iff}\left(\operatorname{And}\left(\operatorname{firstResidual}\left(r, \operatorname{E}\left(d\right), \operatorname{F}\left(d\right), rp, up, vp\right) = 0, \operatorname{secondResidual}\left(r, \operatorname{U}\left(d\right), \operatorname{V}\left(d\right), \operatorname{E}\left(d\right), \operatorname{F}\left(d\right), rp, up, vp\right) = 0\right), \exists a \in \operatorname{ZMod}\left(M\right), \exists aInv \in \operatorname{ZMod}\left(M\right), \operatorname{And}\left(a \cdot aInv = 1, \operatorname{And}\left(rp = a \cdot r, \operatorname{And}\left(up = a \cdot \operatorname{U}\left(d\right), vp = a \cdot \operatorname{V}\left(d\right)\right)\right)\right)\right)\right), \forall mu \in \operatorname{Function}\left(I, \operatorname{Function}\left(\operatorname{ZMod}\left(M\right), \operatorname{Real}\left(\right)\right)\right), \operatorname{sum}\left(I, \operatorname{lambda}\left(i, \operatorname{sum}\left(\operatorname{ZMod}\left(M\right), \operatorname{lambda}\left(rp, \operatorname{ite}\left(\operatorname{And}\left(\operatorname{firstResidual}\left(r, \operatorname{E}\left(d\right), \operatorname{F}\left(d\right), rp, \operatorname{U}\left(i\right), \operatorname{V}\left(i\right)\right) = 0, \operatorname{secondResidual}\left(r, \operatorname{U}\left(d\right), \operatorname{V}\left(d\right), \operatorname{E}\left(d\right), \operatorname{F}\left(d\right), rp, \operatorname{U}\left(i\right), \operatorname{V}\left(i\right)\right) = 0\right), \operatorname{mu}\left(i, rp\right), 0\right)\right)\right)\right)\right) = \operatorname{mu}\left(d, r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ZeckendorfTwoReadTomography.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite indexed family of unimodular rows with the displayed separation property, and every target index d and residue r, both tests vanish on a unimodular candidate exactly when one unit scales its entire triple from the target triple. The proof constructs this scalar and its inverse from the two Bezout certificates; no field instance or target equivalence is assumed.

On distinct projective representatives this joint event is exactly i=d and rp=r. Summing it against any real signed mass mu therefore returns mu(d,r). Nonnegative normalized probabilities are included without adding an assumption needed only for their interpretation.

The experiment family has one designed pair per target. Learning its joint probabilities requires repeated samples or other statistical information. Two observed bits do not encode a whole probability distribution. The complete finite-word construction and the prime-power terminal-rank calculation are proved separately in the existing golden-interface note. The theorem above gives the modular separating events and sums.

Predictive-state and finite Radon-transform background is recorded in Library/notes/singh2004zeckendorfprobability.md: Singh-James-Rudary (UAI2004), Kingston (2006), and Ben-Ari-Miller. Those works are background, not sources of this exact theorem. This is not a claim of an integer Wall-Sun-Sun witness or an independently proved restriction on its initial-depth zero set.

## References

- Truth anchor: `D5/S3/Arith/ZeckendorfTwoReadTomography.firstResidual`
- Truth anchor: `D5/S3/Arith/ZeckendorfTwoReadTomography.result`
- Truth anchor: `D5/S3/Arith/ZeckendorfTwoReadTomography.secondResidual`
