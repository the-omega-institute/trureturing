# Sharp Common Prediction Risk

## Abstract

A sharp threshold for simultaneous deterministic prediction of a two-layer teacher family.

Each of n complete windows is independent with masses (1-3s)/2, s, (1-3s)/2, s, s in alphabet order zero, low, middle, ends, high. Risk is the expectation of a zero-one classification mistake for the original priority teacher.

Coordinates in Fin(n) start at zero. Fix q<r<v with q positive and put m=q.val. TeacherFamily(q) means Bool times Fin(q.val). The family has 2m teachers: (i,q,r) and (i,r,v) for every i<q. In positions numbered from one, these are precisely the teachers (p,q,r) and (p,r,v) with 1<=p<q, and m=q-1.

Let K have binomial law with m trials and success probability 2s. Define G(m,k)=2 min(k,m-k)+min(2k,m-k). The threshold T(m,s) is 8s^2-18s^3+4s^4 plus (s^2/m) times the binomial expectation of G(m,K). The sums include both endpoints k=0 and k=m.

For 0<s<=1/5, one deterministic classifier gives exactly T(m,s) to every teacher. Every deterministic classifier has some teacher whose risk is at least T(m,s). Equivalently, all teacher risks can be at most epsilon simultaneously exactly when T(m,s)<=epsilon.

The common classwise balanced majority classifier has equal errors for all teachers in every rare-count class. Consequently its teacher risks agree for every choice of class weights. This uses one classifier across all classes and all teachers.

The balanced selector attains the pointwise average-risk lower bound. Integrating the three anchors gives an expression in the prefix endpoint count. Its binomial mean produces the explicit threshold. Coordinates outside the selected prefix and three anchors integrate to total mass one, so arbitrary gaps and additional coordinates do not change the threshold.

The result concerns this two-layer subfamily on the independent complete-window law. It does not identify the minimax risk of the family of all increasing triples or of a seam-conditioned input law.

**Theorem 1.1 (Attainment, lower bound and tolerance equivalence).**

$$\forall \left(n: Nat\right), \forall \left(q: \operatorname{Fin}\left(n\right)\right), \forall \left(r: \operatorname{Fin}\left(n\right)\right), \forall \left(v: \operatorname{Fin}\left(n\right)\right), \left(0 < \operatorname{val}\left(q\right)\right) \implies \left(\forall \left(qr: q < r\right), \forall \left(rv: r < v\right), \forall \left(s: Real\right), \left(\left(0 < s\right) \land \left(s \le \frac{1}{5}\right)\right) \implies \left(\left(\exists \left(f: \operatorname{Function}\left(\operatorname{Input}\left(n\right), \operatorname{Fin}\left(3\right)\right)\right), \forall \left(t: \operatorname{TeacherFamily}\left(q\right)\right), \operatorname{gappedRisk}\left(q, r, v, qr, rv, s, f, t\right) = \operatorname{T}\left(\operatorname{val}\left(q\right), s\right)\right) \land \left(\left(\forall \left(f: \operatorname{Function}\left(\operatorname{Input}\left(n\right), \operatorname{Fin}\left(3\right)\right)\right), \exists \left(t: \operatorname{TeacherFamily}\left(q\right)\right), \operatorname{T}\left(\operatorname{val}\left(q\right), s\right) \le \operatorname{gappedRisk}\left(q, r, v, qr, rv, s, f, t\right)\right) \land \left(\forall \left(epsilon: Real\right), \left(\exists \left(f: \operatorname{Function}\left(\operatorname{Input}\left(n\right), \operatorname{Fin}\left(3\right)\right)\right), \forall \left(t: \operatorname{TeacherFamily}\left(q\right)\right), \operatorname{gappedRisk}\left(q, r, v, qr, rv, s, f, t\right) \le epsilon\right) \iff \left(\operatorname{T}\left(\operatorname{val}\left(q\right), s\right) \le epsilon\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk.sharp_risk_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classwise balance gives equal risks under every nonnegative rare-class weight. Pointwise majority attains the average lower bound. The anchor and binomial formulas identify this value with T. A coordinate embedding transports the common classifier to arbitrary ordered anchors, and marginalization removes unused coordinates. Finally the finite teacher family has a risk maximizer, which yields the stated worst-teacher lower bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk.sharp_risk_full`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity](CommonPredictionExteriorCapacity.md)
