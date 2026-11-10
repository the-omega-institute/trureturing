# Two exact circles and saturated evaluation faces

## Abstract

The residual on all original spin inputs

E, its Jordan product, cone, original norm, positive evaluations, P2 and PB are exactly those of OriginalDContract. D is the same arbitrary total function in every inner and outer occurrence. A positive evaluation has arbitrary mass m and vector v with vnorm(v) at most m; P2 retains both directed entries of its complex two-label table. The residual argument selects unit-mass boundary evaluations from this original family. It adds no additivity, homogeneity, continuity, unit-row, translation, three-label positivity or realization premise.

The residual theorem retains one explicit conditional input: there exists a real e, equal to 1 or -1, such that D((0,x),(0,y))=(0,e times cross(x,y)) for every original x,y. It extends that very same e to every scalar/vector input. OriginalPureRigidity.global_pure supplies exactly this premise from the original P2 and PB of the same D. Applying all_inputs_of_pure to that conclusion therefore gives the all-input forward classification with only P2 and PB. The converse and the further same-D consequences are separate assertions.

For fixed e, F(s,t,x,y)=D((s,x),(t,y))-(0,e times cross(x,y)). The known Cayley preimage B of x at q is (x-e times cross(q,x)+dot(q,x) times q)/(1+dot(q,q)). It satisfies B+e cross(q,B)=x and dot(q,B)=dot(q,x). The Cayley image is B-e cross(q,B). All denominators are positive. These are formulas for known vector operations, not an inverse or extension of D.

Take PB on the three pure inputs q,B,C. The two original outer pairs are (-dot(q,C), B+e cross(q,B)), (dot(q,B), C+e cross(q,C)) and their opposite-sign versions. The Jordan correction in the finite difference equals the difference of their fixed cross outputs. Their residuals therefore agree. Applying the existing exact label half-turn restores the original two scalars and negates the opposite Cayley vector images. Every finite q satisfying dot(q,x)=t and dot(q,y)=-s gives a fixed-output residual identity.

An arbitrary determinant-one isometry R fixing k=s x+t y+e cross(x,y) admits the required finite substitution without a continuity argument. If R x=x, the axis equation and preservation of dot(x,y) force R y=y. Otherwise put B=(x-R x)/2, U=(x+R x)/2, C=(y-R y)/2 and V=(y+R y)/2. The equal first norm gives dot(B,U)=0, and the equal mixed Gram entry gives dot(B,V)+dot(U,C)=0. With A=dot(B,B)>0, choose q=(t/A)B+(e/A)cross(B,U). Then dot(q,B)=t and cross(q,B)=e U. The fixed-axis equation gives dot(q,C)=-s and cross(q,C)=e V. Thus the two opposite Cayley images are exactly -R x and -R y. This proves the complete circle law, including identity and half-turn rotations.

Swapping the two original inputs preserves s x+t y and reverses cross(x,y). Skew symmetry of the original D therefore supplies the second complete circle, about s x+t y-e cross(x,y). If cross(x,y) is nonzero and s,t are not both zero, the vector s x+t y is nonzero and perpendicular to cross(x,y). The Gram determinant of these two axes is strictly positive. The supplied TwoAxisFiniteRotation.moving_axis_invariance applies at every actual rotated pair: its two current axes are the images of the original axes. Its exact finite words give fixed-output invariance under every determinant-one isometry. No action is applied to the residual output, and no unknown function is assumed equivariant or continuous.

Write the fixed residual as (delta,z), w=cross(x,y) and p=s y-t x. At a unit n, the original determinant inequality is the squared bound by dot(w+cross(n,p),w+cross(n,p)). Rotating the original inputs and evaluating along the same rotated n leaves the known right side and e dot(n,w) unchanged, while the extra readout becomes dot(R n,z). Twelve explicit determinant-one signed coordinate permutations suffice to compare this extra readout. Four sign choices isolate a single coordinate product, and the three cyclic permutations move every coordinate of n to every coordinate of z. Since some coordinate of a unit three-vector has absolute value at least 1/2, for each coordinate i the resulting bound is abs(delta+e dot(n,w))+(1/2)abs(z_i) at most vnorm(w+cross(n,p)), for every unit n. This finite family is used inside the all-input argument; the input domain and the evaluation family remain unrestricted.

The support calculation takes arbitrary perpendicular w,p with w nonzero. Put a=dot(w,w)>0, b=dot(p,p), c=cross(w,p). When a is at most b, choose n=(c+sqrt(b-a)p)/b. It has squared norm one, dot(n,w)=0 and cross(n,p)=-w, so the support bound reads abs(delta)+Z at most zero. This includes a=b. When b<a, set J=sqrt(a-b) and n_plus=(c+J w)/a, n_minus=(c-J w)/a. Both are unit, dot(n_plus,w)=J, dot(n_minus,w)=-J, and both right-side norms equal J. The two bounds force delta=0 and Z=0 for either e. Taking Z=(1/2)abs(z_i) for each coordinate gives z=0. The case p=0 is included in the second branch.

Collinear vector parts, including either zero vector, use the existing original collinear-zero theorem for every scalar pair. If both scalars vanish, the explicit pure conclusion applies directly. The remaining branch uses the two circles and saturated support. Thus arbitrary signs, unequal lengths, unit vectors, zero and proportional inputs all retain their original values and the one fixed orientation. Matrix consumers, the reverse implication, neutrality, bilinearity, continuity, all finite complex Gram tables and original R require their separate same-D integration.

**Definition 1.1 (Residual in the original output space).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.residual`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalResidual.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every total D, real e,s,t and original vectors x,y, residual(D,e,s,t,x,y) is D((s,x),(t,y)) minus (0,e times cross(x,y)).

**Definition 1.2 (Original coordinates of a known Euclidean rotation).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.rotate`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalResidual.rotate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Euclidean linear isometric equivalence R and original vector x, rotate(R,x) applies R to the same three real coordinates through the standard Euclidean type wrapper and returns the original vector carrier.

**Definition 1.3 (Known finite Cayley inverse formula).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyPreimage`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyPreimage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real e and vectors q,x, the value is (x-e cross(q,x)+dot(q,x)q)/(1+dot(q,q)). When e equals 1 or -1, it is the inverse image of x under v mapping to v+e cross(q,v).

**Definition 1.4 (Opposite Cayley image).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyImage`

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real e and vectors q,x, put B=cayleyPreimage(e,q,x). The image is B-e cross(q,B).

**Theorem 1.5 (Pure PB triples fix the Cayley residual).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayley_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalResidual.cayley_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every total D satisfying original P2 and PB, real e equal to 1 or -1, and the same-D pure formula for every x,y, the following holds for every real s,t and all x,y,q satisfying dot(q,x)=t and dot(q,y)=-s: F(s,t,x,y)=F(s,t,-cayleyImage(e,q,x),-cayleyImage(e,q,y)). No nonzero, independence or scalar restriction is imposed on this finite-parameter law.

**Theorem 1.6 (Every rotation about the first residual axis).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.local_full_circle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalResidual.local_full_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying original P2 and PB, real e equal to 1 or -1 and its same-D all-pure formula, every real s,t, every x,y with cross(x,y) nonzero, and every determinant-one Euclidean isometry R fixing s x+t y+e cross(x,y), one has F(s,t,rotate(R,x),rotate(R,y))=F(s,t,x,y). The identity rotation is included and s,t may both be zero. The second axis follows by swapping the two original inputs and using skew symmetry.

**Theorem 1.7 (Saturated faces eliminate a fixed additive residual).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.saturated_support_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalResidual.saturated_support_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real e,delta,Z with e equal to 1 or -1 and Z nonnegative, and every nonzero original vector w and perpendicular vector p, suppose for every unit vector n that abs(delta+e dot(n,w))+Z is at most vnorm(w+cross(n,p)). Then delta=0 and Z=0. The vector p may vanish, and all comparisons of the two vector lengths, including equality, are included.

**Theorem 1.8 (One pure sign extends to all original scalar/vector inputs).**

Lean statement: `D5/S3/Quantum/SpinFactor/OriginalResidual.all_inputs_of_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalResidual.all_inputs_of_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary total D on the original E, assume the original all-evaluation directed complex P2, the literal same-D PB, and the explicit conclusion that there exists a real e equal to 1 or -1 with D((0,x),(0,y))=(0,e cross(x,y)) for every x,y. Then there exists such an e with D((s,x),(t,y))=(0,e cross(x,y)) for all real s,t and all original x,y. The proof retains the sign selected by the pure premise and handles every degenerate input. There is no additional geometric, regularity or physical premise. The pure premise is supplied by OriginalPureRigidity.global_pure with only the original P2 and PB. Their exact composition gives the forward classification; the reverse implication and further same-D consequences remain separate assertions.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.all_inputs_of_pure`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyImage`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayleyPreimage`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.cayley_residual`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.local_full_circle`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.residual`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.rotate`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalResidual.saturated_support_zero`
- Dependency: [D5/S3/Geometry/TwoAxisFiniteRotation](../../Geometry/TwoAxisFiniteRotation.md)
- Dependency: [D5/S3/Quantum/SpinFactor/OriginalDContract](OriginalDContract.md)
