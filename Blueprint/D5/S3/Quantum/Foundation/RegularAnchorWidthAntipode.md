# Full original width and antipodal contact

## Abstract

The entire original effect interval detects actual antipodal contact and unit support at a regular anchor.

Keep the original finite dimensional real carrier V, closed generating cone C, strictly positive unit u, complete base K and full effect interval 0 <= f <= u. Every original exclusion has a full three-ball chart, and equality of exclusions identifies their pure labels. At the original regular anchor p the actual common confirmer e is unique. The NativeChart input is derived by RegularAnchorNormalChart.regular_anchor_native from precisely these original hypotheses; it supplies neither a free positivity bridge nor a chosen subfamily of effects.

**Definition 1.1 (Entire actual ratio image).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actualImage`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actualImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z is the image of every x in K other than p under H(x)/g(x), where g=u-e. NativeChart proves g is positive on this entire domain. No closedness of the pure state carrier is assumed.

**Definition 1.2 (Actual directional support).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho(v) is the supremum of -inner(v,z) over the whole actual ratio image. It is the exact source supremum of -inner(v,H(x))/g(x) over all x in K other than p.

**Theorem 1.3 (Whole actual image is bounded).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actual_image_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actual_image_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a finite positive M bounding the norm of every actual ratio image. Divide the proved whole-cone NativeChart bound by the strictly positive gap on K except p.

**Theorem 1.4 (The whole inner ball is actual).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.ball_subset_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.ball_subset_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector w in the closed unit ball is the ratio image of the actual state a(w), with gap exactly one. This state cannot equal p, whose gap is zero.

**Theorem 1.5 (Every full support supremum is bounded).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_values_bdd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_values_bdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vector v the entire set of support readings on Z is bounded above by norm(v)*M. The real supremum therefore has its ordinary upper-bound meaning.

**Theorem 1.6 (Whole-base support bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_le_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r and every coordinate vector v, rho(v)<=r is equivalent to -inner(v,H(x))<=r*g(x) for every original base state x other than p. The whole-cone NativeChart bound proves that the defining supremum is finite.

**Theorem 1.7 (Actual inner-ball lower bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_unit_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_unit_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit v, rho(v)>=1 because the actual original chart point a(-v) has g=1 and H=-v. This uses an actual state in the original exclusion.

**Definition 1.8 (Original directional linear effect).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.direction`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real linear functional direction(v) on V is inner(v,H). Its coordinate expansion lies in the entire signed normal span. The proved restriction isomorphism, rather than an additional premise, reconstructs every normalized positive annihilator with slope v as g+direction(v).

**Theorem 1.9 (Exact actual antipodal criterion).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_one_iff_antipodal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_one_iff_antipodal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit v, rho(v)=1 exactly when some effect in the entire original interval takes one at a(v) and zero at a(-v). Positivity is derived on the full original cone from the ratio bound; conversely an arbitrary original separating effect enters the existing actual comparison and slope-body theorem. The source direction v and the actual chart antipodes are retained without reversing or replacing their carriers.

**Definition 1.10 (Entire exclusion oscillation).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.oscillation`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.oscillation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Oscillation is the supremum of f on the entire original exclusion minus its infimum there. Every original real linear effect is continuous in the finite dimensional topology. The exact affine slope formula proves that this difference equals twice the Euclidean norm of its actual chart slope, including constant restrictions.

**Definition 1.11 (Full original effect width).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(D(p)) is the supremum of the entire-exclusion oscillation over all effects in the full original interval 0<=f<=u. The attainment theorem proves this is the source maximum, so the supremum notation does not weaken the source definition or remove an effect.

**Theorem 1.12 (Actual full-effect width attainment).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist a real linear effect f on the original carrier and a unit coordinate vector v such that W(D(p))=f(a(v))-f(a(-v)). The same actual f maximizes at a(v) and minimizes at a(-v) over the whole exclusion. Compactness of the full effect interval and continuity of twice the slope norm give the effect; the affine formula gives its antipodal extrema.

**Theorem 1.13 (Exact width and actual unit-support equivalence).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_one_iff_rho_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_one_iff_rho_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Width equals one if and only if an actual unit direction v satisfies rho(v)=1. If width is one, its attaining effect has actual readings one and zero at its antipodal extrema. Conversely any effect supplied by the unit-support criterion gives a full-exclusion oscillation of at least one, while every original effect has oscillation at most one. All quantifiers range over the original cone, base, effect interval and actual full chart.

These results are an intermediate mathematical interface for Theorem 122.13. The minimum over the entire sphere, the closure shell and boundary criterion, strict delta containment and boundary distance require the remaining original clauses. No whole-theorem completion, matrix realization, physical operation, literature novelty or completed four-slot registration is asserted here.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actualImage`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.actual_image_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.ball_subset_actual`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.direction`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.oscillation`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_le_iff`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_one_iff_antipodal`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_unit_lower`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.rho_values_bdd`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_attained`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.width_one_iff_rho_one`
- Dependency: [D5/S3/Quantum/Foundation/RegularAnchorNormalChart](RegularAnchorNormalChart.md)
