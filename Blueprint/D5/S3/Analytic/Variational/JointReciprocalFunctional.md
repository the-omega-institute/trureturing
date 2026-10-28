# Joint Reciprocal Functional

## Abstract

The joint reciprocal functional has an explicit smooth increasing minimizer and exact attained infima over the full bounded positive measurable class.

The cited supplier-relative paper supplies the original analytic construction and JVM1--JVM2 target. This formalization proves only scalar-coordinate existence, the explicit normalized profile and the full measurable-class variational values. It does not verify the paper's source-window, arithmetic, strict-gain, Robin or RH claims. The scalar-coordinate support retains the original Lean constant names so the three public theorem statements remain identical.

**Definition 1.1 (Competitor mass).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.mass`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.mass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real function u on the real line, mass(u) is its oriented Lebesgue integral from 1 to 2.

**Definition 1.2 (Cumulative competitor mass).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.primitive`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.primitive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real function u and every real x, primitive(u,x) is the oriented Lebesgue integral of u from 1 to x.

**Definition 1.3 (The joint reciprocal cost).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.cost`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.cost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b and real function u, cost(b,u) is b times the integral of x/u(x) from 1 to 2 plus the integral of primitive(u,x)/(u(x)^2) over the same interval.

**Definition 1.4 (The full bounded positive measurable class).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.Admissible`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

A real function u is admissible when it is almost everywhere measurable for Lebesgue measure restricted to [1,2], and there exist real c and B with c>0 and c<=u(x)<=B almost everywhere there. The bounds belong to u; no fixed common bounds or smoothness condition is imposed. This includes every Lebesgue measurable function in the stated class and all modifications on null sets.

**Definition 1.5 (The selected scalar endpoint).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.scalarRoot`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.scalarRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b, scalarRoot(b) is the inverse integral coordinate at log(2). The inverse is chosen on (-epsilon,upperRoot(b)), where epsilon is the minimum of lowerRoot(b)/2 and b/6. For 0<b<=1 the coordinate is injective on this open interval and the chosen inverse is its actual inverse at every attained value.

**Definition 1.6 (The sharp variational value).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharpConstant`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharpConstant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b, sharpConstant(b) is 8 times scalarRoot(b) squared times [b+2 scalarRoot(b)].

**Definition 1.7 (The explicit normalized profile).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.optimizer`

*Formalization.* `D5/S3/Analytic/Variational/JointReciprocalFunctional.optimizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For real b and x, let v(x) be the same inverse integral coordinate applied to log(x), and let vb=scalarRoot(b). The profile optimizer(b,x) is x squared times polynomial(b,v(x)), divided by 8 vb polynomial(b,vb). Its existence uses no differential equation solution or normalization hypothesis.

**Theorem 1.8 (Existence and uniqueness of the original scalar root).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.exists_unique_scalar_root`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalFunctional.exists_unique_scalar_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, there is exactly one real v with 0<v<upperRoot(b) and coordinate(b,v)=log(2). The proof factors the denominator as 6[upperRoot(b)-v][v+lowerRoot(b)], identifies a logarithmic antiderivative, proves its divergence at the positive root, and uses strict monotonicity and the intermediate value theorem. The endpoint b=1 remains in scope.

**Theorem 1.9 (Smooth construction, normalization and exact cost).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.constructed_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalFunctional.constructed_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, scalarRoot(b) is positive, is less than upperRoot(b), solves the original integral equation, and sharpConstant(b)>0. There is an open subset s of the real line containing [1,2] on which optimizer(b) is infinitely continuously differentiable, positive and strictly increasing. This profile is admissible, has mass one, and has cost exactly sharpConstant(b). To obtain smoothness, local inverse uniqueness identifies the chosen inverse with the smooth local inverses. Direct differentiation of x optimizer(b,x) v(x) gives optimizer(b,x), proving normalization. Direct differentiation of x squared times [b v(x)+2v(x) squared] divided by optimizer(b,x) gives the full cost density, and its endpoint difference is the exact value. For every admissible function u, the individual upper and positive lower bounds imply integrability of u and x/u. The cumulative mass is continuous on [1,2], and its boundedness together with the positive lower bound gives integrability of primitive(u,x)/(u(x)^2). These integral facts are used in the cost calculation. The sharp variational theorem compares this profile with every admissible measurable competitor.

**Theorem 1.10 (Sharp attained variational values on the full measurable class).**

Lean statement: `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharp_joint_variational`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharp_joint_variational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Actual Robin price gaps, forced-core tail records and the selected-sign boundary*. URL: <https://github.com/the-omega-institute/trureturing/blob/0d8903a599ca95dc10b460e31a72cc1ebfc3433b/Library/ArithSums/trureturing2026extrawindowpairing.md>.

*Commentary.*

For every real b with 0<b<=1, let C=sharpConstant(b)>0. Every admissible u satisfies mass(u)*cost(b,u)>=C. The set of all these product values has least element and infimum C. Every positive scalar multiple of the constructed optimizer belongs to the same class and attains this product value. For every real d>0, the set of values d/8 times [4 mass(u)+cost(b,u)] has least element and infimum d/2 times sqrt(C). The admissible function sqrt(C)/2 times optimizer(b) attains that scalar value. The individual upper and strictly positive lower bounds vary with u; the comparison imposes no smoothness, common bounds, or inverse-function assumption on u.

For mass-one competitors, U is absolutely continuous with derivative u almost everywhere and range in [0,1]. Only the smooth profile primitive W is inverted. Its inverse X is the unique inverse of W on its open positive domain; local inverse uniqueness gives smoothness of this same X. Put Z(r)=X(r)*sqrt(X(r)), Q(r)=3 sqrt(X(r))/(2 optimizer(b,X(r))), M(r)=4b sqrt(X(r))/(3 optimizer(b,X(r)))+2r/(sqrt(X(r))*optimizer(b,X(r)) squared), and N(r)=-r/(X(r)*sqrt(X(r))*optimizer(b,X(r)) cubed). Direct differentiation of the constructed profile proves M'=N and Z'=Q.

For nonnegative r and q and positive z, Z and Q, the functional density F(r,z,q)=4bq squared/9+8rq cubed/(27z) lies above its tangent plane at (Z,Q). The cubic tangent gap follows from two polynomial cases: if q<=Q/3 all remaining terms are nonnegative; otherwise four times the denominator-cleared gap is Q times (2Qz-3qZ+QZ) squared plus Z squared times (q-Q) squared times (4q-Q). The quadratic tangent gap is 4b(q-Q) squared/9.

The comparison function V(x)=M(U(x)) times [x sqrt(x)-Z(U(x))/2] is absolutely continuous: the calibration coefficients are smooth on a neighborhood of the compact range of U and therefore Lipschitz there. The a.e. chain and product rules and the tangent inequality give V'(x)<=b x/u(x)+U(x)/u(x) squared. The endpoint difference equals the difference of M(W(x))*x sqrt(x)/2 at 2 and 1. Direct differentiation of this latter smooth function gives the profile cost density, so the fundamental theorem of calculus proves cost(b,u)>=C. All integrability facts follow from the original bounds. Positive scaling then removes normalization. Finally, mass(u)>0 and the square (2 mass(u)-sqrt(C)) squared combine with the product bound to give 4 mass(u)+cost(b,u)>=4 sqrt(C); the stated scaled profile attains equality. These are analytic variational values, with no claim of arithmetic attainability, a strict Robin inequality above 5040, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.Admissible`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.constructed_profile`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.cost`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.exists_unique_scalar_root`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.mass`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.optimizer`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.primitive`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.scalarRoot`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharpConstant`
- Truth anchor: `D5/S3/Analytic/Variational/JointReciprocalFunctional.sharp_joint_variational`
- Dependency: [D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate](JointReciprocalScalarCoordinate.md)
