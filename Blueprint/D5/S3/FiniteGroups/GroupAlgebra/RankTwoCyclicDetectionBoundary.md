# Cyclic Subgroups Do Not Detect Projectivity

## Abstract

An explicit six-dimensional modular action refutes projectivity detection by all actual cyclic subgroups.

**Theorem 1.1 (A closed refutation over the field with three elements).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_fails`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed proposition cyclic_projectivity_detection_claim asserts the following universal implication for the fixed F, E and V: for every representation tau of E on V over F, if for every actual subgroup H of E the assumption IsCyclic H implies projectivity of the actual restriction tau composed with H.subtype over F[H], then tau.asModule is projective over F[E]. The sole bound result cyclic_projectivity_detection_fails is exactly Not cyclic_projectivity_detection_claim. Its proof applies the asserted detector to the concrete rho, supplies all actual cyclic restrictions, and derives a contradiction from the ambient norm obstruction. The claim quantifies over every representation on these fixed types; rho is its concrete counterexample.

Let F=ZMod 3, E=Multiplicative(F times F), W=F times F and V=W times (W times W), with ordered blocks v0,v1,v2. The displayed representation rho is projective over F[H] for every actual cyclic subgroup H of E, using rho composed with the actual inclusion H.subtype. Its actual F[E]-module is not projective. The quantifier includes the trivial subgroup and every choice of nontrivial cyclic subgroup; there is no assumption about a selected pair of generators.

Write J(x,y)=(-y,x), so J squared is minus the identity. Set N(v0,v1,v2)=(v1,v2,0), S=I+N and T=I+Jbar N. With c(a)=2(a squared minus a), L=aI+bJ and Q=(c(a)-c(b))I+abJ, the explicit action is rho(a,b)(v0,v1,v2)=(v0+Lv1+Qv2,v1+Lv2,v2). This is exactly S to the residue a times T to the residue b. The polynomial formula directly proves the representation laws over F; it fixes both the block order and the sign of J.

For every nonzero pair (a,b), Delta=a squared plus b squared satisfies Delta squared equals one. Consequently Delta(aI-bJ) inverts L, while (a squared minus b squared)I+abJ inverts L squared. These formulas hold uniformly in all eight nonzero directions. Fixedness under such an element first forces Lv2=0 and then Lv1=0, so its fixed space is exactly the vectors (w,0,0). Conversely, the action formula fixes every vector of that form.

As mathematical context rather than additional Lean theorems, Delta=a squared plus b squared is the anisotropic norm from F9 to F3. Identifying (x,y) with x+i*y for i squared equals minus one makes J multiplication by i; identifying the three blocks with v2+v1*t+v0*t squared in F9[t]/(t cubed) makes N multiplication by t. After scalar extension the restriction-of-scalars module splits into two Frobenius summands: S-I acts as diag(N,N), and T-I as diag(i*N,-i*N). A shifted direction alpha*(S-I)+beta*(T-I) is singular on one summand precisely on the conjugate lines alpha+beta*i=0 or alpha-beta*i=0. Their union has equation alpha squared plus beta squared equals zero and contains no nonzero F3-rational point, explaining the determinant form used by the uniform inverse proof. At (-i,1) one summand is trivial and the other is free; the whole module is not trivial. Shifted directions differ from actual subgroup elements S to the a times T to the b: the formal proof below uses the complete actual-subgroup argument. This explanation adds no formal field-extension, general-prime or minimal-dimension claim.

Choose a generator h of an arbitrary actual cyclic subgroup H. If h is the identity, H has one element and its norm is the identity. Otherwise h has order three, and the bijection i maps to h to the power i from Fin 3 onto H reindexes the actual subgroup sum. For h=(a,b), this norm is I+rho(h)+rho(h squared), equal to (rho(h)-I) squared; on coordinates it sends v to (L squared v2,0,0). Thus (w,0,0) has the explicit norm preimage (0,0,((a squared minus b squared)I+abJ)w). The imported projective_iff_projective_invariants_and_norm_surjective theorem, with p=3 and exponent one, applies to H as an actual subgroup of the three-group E. Its invariant coefficient space is projective because F is a field. This proves projectivity for every cyclic restriction.

For E itself the literal sum over all nine group elements is zero. Equivalently, its two norm factors are (I+S+S squared)=N squared and (I+T+T squared)=-N squared, whose product vanishes. The coordinate proof sums the explicit polynomial action over both field coordinates. The vector ((1,0),0,0) is nevertheless nonzero and fixed by every element of E. Applying the necessary direction of the same imported norm criterion would require a preimage of this vector under the zero norm. Its first scalar coordinate gives the contradiction zero equals one.

This directly constructed example makes no historical priority or novelty claim. It shows why an ambient cyclic hypothesis in a cyclic prime-support projectivity detector cannot simply be removed, even for abelian groups and even when all actual cyclic subgroups are tested. For elementary-abelian detection, E itself is elementary abelian of rank two and belongs to the required test family. There is therefore no conflict with Chouinard detection. The contextual source is Eli Aljadeff, Profinite groups, profinite completions and a conjecture of Moore, arXiv:math/0405201, Theorem 2.4 (https://arxiv.org/abs/math/0405201); that source is cited for elementary-abelian detection, not as an attribution of these exact matrices.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/RankTwoCyclicDetectionBoundary.cyclic_projectivity_detection_fails`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing](PGroupProjectiveNormRing.md)
