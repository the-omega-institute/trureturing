# Original-unit lift images

## Abstract

Retaining the original unit gives a closed cone lift, its exact minimum-cost perspective and the full compact convex normalized readout image.

This is the cone-geometric theorem used by Proposition 123.8 of Quantum Origin Same Readback and Parallel Reset Calibration, with an arbitrary real normed readout space W. The quantum coordinates use W=R cubed. V is any finite dimensional real normed carrier; C is its entire closed pointed cone and u is strictly positive on every nonzero cone vector. The original p belongs to the whole base K={x in C : u(x)=1}. The original linear g is nonnegative on all C and vanishes at p; the original linear H vanishes at p. Every cone vector with g=0 is a nonnegative multiple of p. These are the original zero-face facts supplied before Proposition 123.8, rather than a hypothesis of attainment or closedness of the projected image. No EB3 model is substituted for those data: the cone theorem applies before the choice of a matrix model, and makes no assertion of the other native quantum hypotheses.

For the exact original application, K is CircuitBalancedConfirmation.base C u, P is its entire pure set, and the effect interval is the entire proper C u interval. D_p is FacetZeroGluing.exclusion C u p, including every original mixed state in that exclusion. The source inputs are the same closed pointed generating cone, strictly positive original unit, a whole three-ball chart for every original pure label, and injectivity of the full exclusion-label map. OriginalNormalRestriction.original_normal_restriction supplies an interior positive annihilator whose restriction to the entire chart is constant one. Its full constant-one fiber identity supplies an original e in OrthogonalJointCompletion.common C u p, so e is proper, e(p)=1 and e vanishes on every point of D_p. OriginalWidthContact.top_subsingleton_of_zero_exclusion applies to every such e, using precisely its properness and its zero values on the entire D_p. Since p belongs to its one-value face, subsingletonness gives the full identity {x in K : e(x)=1}={p}, including all mixed states. At the source anchor p in P_reg, the original singleton property of A_p identifies this supplied e with the specified e_p. Set g literally equal to u-e_p. The continuity part of P_reg is unnecessary for this pointwise application; no Pair or global classification premise is introduced.

Write the original affine chart a as c+B(w), with c=a(0) and B its linear part. Injectivity of a gives injectivity of B, and its whole-image identity is exactly D_p={c+B(w) : norm(w)<=1}. The same normal-restriction theorem makes restriction from the full continuous-dual span of positive annihilators onto all affine functionals on Euclidean R cubed surjective. Apply that surjectivity to each coordinate projection, obtaining three original span elements f_i whose restrictions are w_i for every w. The canonical map from continuous linear functionals to real linear functionals sends this span into S_p=span N_p, where N_p is CommonPositiveExtension.zeroPositive C u p. Assemble H from the three f_i. Thus H(c+B(w))=w on the entire affine chart, and each H_i belongs to the original S_p. These are derived chart/readback data, with no assumed generic zero ray or independently supplied coordinate extension. Properness of e_p gives g>=0 on C, while u(p)=e_p(p)=1 gives g(p)=0. Evaluation at p kills N_p, hence its entire real span by the kernel/span inclusion; this gives each H_i(p)=0 and H(p)=0. For any nonzero original y in C with g(y)=0, strict positivity permits the original normalization x=y/u(y). Then x belongs to the same K and e_p(x)=1, so the full one-value-face identity gives x=p and y=u(y)p. The zero vector supplies the remaining endpoint of the nonnegative p ray.

Under this parameter correspondence, Z_p is exactly all H(x)/g(x) with x in the entire original K except p. The extended cost Lambda_p is the extended-real infimum of the same u over every y in the original C with g(y)=1 and H(y)=z. Attainment identifies that infimum with unitCost on the feasible domain; outside the domain the fiber is empty and both are positive infinity. The perspective and unit-slice formulas therefore use the actual Z_p, Lambda_p and original u. Set L=(span N_p).dualCoannihilator, the original annihilator in V. The same evaluation/kernel argument proves p belongs to this particular L, so the quotient non-descent conclusion applies to V/L itself. The application needs no normal-space restriction isomorphism, positive section, matrix model, residual continuity or boundary support-point cost identity.

**Definition 1.1 (All feasible original lifts).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.fiber`

*Formalization.* `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every z in W, the fiber contains every y in the same C with g(y)=1 and H(y)=z. No selected finite readout, effect menu or sampling is used.

**Definition 1.2 (Entire feasible readout domain).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.domain`

*Formalization.* `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.domain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The whole domain consists of the z with a nonempty full lift fiber. The theorem identifies it with all H(x)/g(x) for original normalized x distinct from p; g is strictly positive at each such x by the original zero-face hypothesis.

**Definition 1.3 (Feasible original unit infimum).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.leastUnit`

*Formalization.* `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.leastUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real infimum of u over the entire original fiber. Its real value is used only on the feasible domain, where the theorem proves an actual global minimizer.

**Definition 1.4 (Extended original unit cost).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unitCost`

*Formalization.* `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unitCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extended real cost is the real fiber infimum on its entire feasible domain and positive infinity off the domain. The same original u supplies every cost. It is not a new functional on a quotient.

**Definition 1.5 (Keep the original unit coordinate).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.liftMap`

*Formalization.* `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.liftMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear map sends every original y to (u(y),g(y),H(y)). In particular p has image (1,0,0), whereas zero has image (0,0,0).

**Theorem 1.6 (Closed cone, exact cost perspective and entire unit slice).**

Lean statement: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unit_preserving_lift_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unit_preserving_lift_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated whole-cone hypotheses, the full image of C under (u,g,H) is closed and convex and is stable under every nonnegative scalar. For all real t,s and every z in W, (t,s,z) belongs exactly when either t>=0 and s=z=0, or s>0, z/s is feasible and s times its least original unit cost is at most t. Thus the zero-mass ray and every positive-mass fiber are both retained, including their endpoints. The entire normalized image (g,H)(K) is compact and convex. Its membership criterion is exactly the preceding criterion at t=1, with the zero point included. Every feasible cost is attained by an actual y in C, and that same y is no more expensive than any other feasible original lift. The domain is exactly the normalized original ratio image. Finally, for every real submodule L containing p, u cannot factor through the quotient by L: the quotient kills p while u(p)=1.

The existing mass_cap_compact and base_compact statements supply full original compact caps. For a fixed feasible readout, intersect one such cap with the closed full readout fiber; its continuous minimum is global because every cheaper candidate lies in that cap. For a convergent sequence of full lifted readings, the retained unit coordinate bounds all original preimages in one such cap. A convergent original subsequence then lifts the limiting reading, proving closedness even though the original cone is unbounded. To realize every point above the cost perspective, scale an actual minimum lift by s and add (t-s times its cost) p. This addition changes only the original unit coordinate and stays inside the same cone. It constructs each required point separately and supplies no linear selection of minimizers.

The exact formulas include the entire original mixed base and every cone point. No positive linear section, positive retraction, common preparation, physical instrument or dynamics follows. Neither a global upper bound on costs nor cost-one contact with an original ball is assumed or proved here. The cost-layer and actual support-point identities of Theorem 123.7 and the boundary minimum of Definition 123.9 remain separate obligations. This is a repository-derived cone statement using pinned compactness and subsequence results; literature priority is not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.domain`
- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.fiber`
- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.leastUnit`
- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.liftMap`
- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unitCost`
- Truth anchor: `D5/S3/Quantum/Foundation/UnitPreservingLiftImage.unit_preserving_lift_image`
- Dependency: [D5/S3/Quantum/Foundation/RealRogFailureQuantitative](RealRogFailureQuantitative.md)
