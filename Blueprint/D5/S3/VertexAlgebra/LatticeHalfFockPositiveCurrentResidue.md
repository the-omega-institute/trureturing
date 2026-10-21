# Positive Current Residues

## Abstract

Complete actual positive-current residue and unweighted original-source tail.

Let D be arbitrary LatticeData, hu:IsUnit D.G.det, i:Fin D.rank, b:Carrier D, gamma,t integers, s a natural number, and x:ActualTensor(D,hu). The source Carrier D and the actual tensor module are distinct carriers. Set N=vectorFrequencyBound(D,b)+1, A(q)=tensorCurrent(D,ActualGround(D,hu),i,q), and B(v)=(correctedField(D,hu,b)).coeff(-2*v-gamma-2). Reuse currentResidue from LatticeHalfFockNegativeCurrentResidue: R(r,t,x) is the natural-index finsum of (-1)^l choose(r,l) A(r-l)(B(t+l)x), minus the signed integer power (-1)^r times the finsum of (-1)^l choose(r,l) B(r+t-l)(A(l)x). Neither ordering is discarded.

The existing current_residue_left_finite and current_residue_right_finite supply actual-input support: the first uses the Hahn order of the field on x before applying the current, and the second uses current truncation on x before the field coefficient acts. For r=s>=0, choose(s,l)=0 when l>s restricts both sums to range(s+1). These statements concern the input x and its actual transformed vectors; they assert no global finite endomorphism support, and no unsupported infinite exchange is used.

Reflect the second finite ordering by l -> s-l. On 0<=l<=s, Nat.choose_symm preserves the binomial coefficient and (-1)^s*(-1)^(s-l)=(-1)^l. The reflected field exponent -2*(s+t-(s-l))-gamma-2 equals -2*(t+l)-gamma-2 literally. The complete residue becomes the finite weighted sum of the commutator of A(s-l) with this field coefficient. Apply correctedField_current_ward without an extra desired-law premise, with q=s-l and e=-2*(t+l)-gamma-2. Its original-source range is range N, including n=0, and e-(2*q+1)+2*n=-2*(t+s-n)-gamma-3 is independent of l.

Only finite sums are then exchanged. The consumed scalar helper proves, for arbitrary complex a and natural s,n, sum_l choose(s,l)*(-1)^l*Ring.choose(s-l+a,n)=if s<=n then Ring.choose(a,n-s) else 0. Finset.sum_choose_succ_mul and Ring.choose_succ_succ reduce the difference order and binomial degree together; degree zero cancels at every positive difference order. Specializing a=1/2 yields the operator coefficient. The explicit zero branch is necessary: natural subtraction alone would replace n-s by zero below the diagonal and introduce false terms.

**Theorem 1.1 (The complete nonnegative residue is the finite neutral-mode sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the complete telescope D,hu,i,b,gamma,t,s,x above, currentResidue(D,hu,i,correctedField(D,hu,b),gamma,(s:Int),t,x) equals the sum over n in range N of: if s<=n, Ring.choose((1/2:Complex),n-s) times (correctedField(D,hu,neutralMode(D,i,(n:Int),b))).coeff(-2*(t+(s:Int)-(n:Int))-gamma-3)x; otherwise zero. The identity covers s=0, n=0, zero source and zero charge, and arbitrary finite sums in the actual tensor module. No sector, eigenstate, homogeneity, vacuum, positive lattice, locality, or module-law restriction is assumed. For rank zero there is no i:Fin D.rank, and no nonempty-rank hypothesis is added.

**Theorem 1.2 (The complete unweighted residue vanishes at the original source cutoff).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue_tail`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every natural s with vectorFrequencyBound(D,b)+1<=s, all integer gamma,t and every actual x, currentResidue(D,hu,i,correctedField(D,hu,b),gamma,(s:Int),t,x)=0. Every retained n satisfies n<N<=s, so the explicit zero branch of the exact finite residue identity applies. This is cancellation of the complete residue. It does not assert that either ordered half separately vanishes, and it uses the cutoff of the original source b rather than that of corrected sources. No binomial weight on an outer tail is substituted for this unweighted assertion.

These are repository-derived finite coefficient calculations in the classical twisted-lattice setting described by Bakalov and Kac, Twisted Modules over Lattice Vertex Algebras, math/0402315. They supply the positive outer residue and its source cutoff. The negative outer convolution and Ward law are reused from their existing owners. Full current iteration at every cutoff, separate-source twisted module reconstruction, charged closure, and the Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme require further results. No physical realization or completion of that programme is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPositiveCurrentResidue.correctedField_positive_current_residue_tail`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard](LatticeHalfFockCurrentWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue](LatticeHalfFockNegativeCurrentResidue.md)
