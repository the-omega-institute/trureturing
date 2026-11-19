# Pure exhaustion on the full original carrier

## Abstract

Pure-point exhaustion restores the original mixed comparison and complementary least effects.

The carrier is a nonzero finite-dimensional real normed space with a closed pointed generating cone C and a unit u strictly positive on nonzero cone points. The normalized base is the entire original base C intersected with u=1, and pure points are every extreme point of that base. Effects are the complete original interval of linear maps f with 0<=f<=u on the whole cone. No finiteness, closedness, or exposedness assumption is made on the pure-point set.

ContinuousFrameSum.effects_compact gives compactness of the complete proper-effect interval. Each confirming face is a nonempty closed slice of that compact set. ExclusionWidthCompactness.comparison_attained supplies a minimizing original confirmer at every input. The pure-pair relation makes the opposing comparison zero.

For fixed pure p and q, assume only the pure relation T_p(r)+T_q(r)=1 for every original extreme point r. Every pair of confirming effects then gives a closed halfspace containing all pure points. Krein–Milman closure extends these inequalities to the entire original base; an attained confirmer for q that vanishes at p supplies the opposite upper bound. Thus the relation holds on every mixed original state and restricts back to the pure relation.

The lower envelopes are affine on every finite pure convex combination because each is concave and their sum is constant. Signed finite relations are normalized by positive and negative parts, with the zero vector and zero coefficients retained; the existing full-pure circuit descent then supplies linear effects e_p and e_q. Pure bounds extend to the whole cone, so each effect is proper, confirms its reference, and is least against every original confirmer. They agree with the attained comparison on the entire cone, and pure spanning gives e_p+e_q=u. The same argument forces p!=q and produces an attained confirmer for q whose value at p is zero.

**Theorem 1.1 (Every confirming face is compact).**

Lean statement: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.face_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.face_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original pure point p, the complete confirming face is compact and nonempty, and evaluation at p exposes it in the original effect interval.

**Definition 1.2 (Pure-only complementary comparison relation).**

Lean statement: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.purePairRelation`

*Formalization.* `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.purePairRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed original pure p and q, purePairRelation is the exact premise T_p(r)+T_q(r)=1 for every extreme point r of the entire original base.

**Theorem 1.3 (Pure and mixed complementary comparison agree).**

Lean statement: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_pair_relation_iff_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_pair_relation_iff_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original closed cone, strictly positive unit and generating-span hypotheses, the sum of the comparisons of p and q is one on every original pure point exactly when it is one on every point of the normalized base. The reverse implication restricts to pure points in that base.

**Theorem 1.4 (Pure exhaustion yields mixed equality and complementary least effects).**

Lean statement: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_exhaustion_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_exhaustion_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under purePairRelation, p and q are distinct; an attained confirmer for q vanishes at p; the comparison sum is one on every mixed point of the original base; and linear effects e_p,e_q are proper, confirm their references, least on the whole cone, equal the attained comparisons on the whole cone, and satisfy e_p+e_q=u. This entry does not claim the later ball, compact-closure/Haar, same-H control-group, 98.4, or 98.5 resource conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.face_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.purePairRelation`
- Truth anchor: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_exhaustion_entry`
- Truth anchor: `D5/S3/Quantum/Foundation/PureExhaustionConfirmation.pure_pair_relation_iff_mixed`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionWidthCompactness](ExclusionWidthCompactness.md)
