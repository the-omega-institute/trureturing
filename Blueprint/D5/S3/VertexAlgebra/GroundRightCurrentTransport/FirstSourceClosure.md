# FirstSourceClosure

## Abstract

First-source original-mu closure

The source mu, correctedField, ActualTensor and all unreduced signed lifts are unchanged. Source Borcherds at (p,q,r)=(0,r,d) is applied to current,a,b and mapped by the actual linear source-to-slice map. A common K majorizes both a genuine target A/B locality order and an independently obtained original source-vector tail. Target locality alone is never used to assert source-vector vanishing.

Smaller compatibility identifies Q(A,B) with the slice of the actual source mu. This identification supplies H2 from actual current/source locality, without an assumed general Dong theorem. The same-numerator nested iterate and native_current_inverse then identify both finite source Borcherds sums. Every native defect vanishes, and defect_compatible restores all signed coefficient laws and their three finite supports.

**Theorem 1.1 (Closure under an actual first-source current).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_current_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_current_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D, unit determinant hu, current i, original a and signed gamma, the sole induction hypothesis is OriginalCompatible(a,b,gamma,delta) for every original b and signed delta. For every signed current mode d the conclusion is OriginalCompatible(neutralMode(i,d,a),b,gamma+1,delta). In particular d=-m gives negative-current closure; the lift changes once independently of m.

**Theorem 1.2 (Matching first eigensource and arbitrary second source).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_eigen_arbitrary_second`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_eigen_arbitrary_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D, unit determinant hu, original a and signed gamma satisfying theta(a)=(-1)^gamma a, every arbitrary original b and signed delta satisfies OriginalCompatible(a,b,gamma,delta). The matching first eigenvalue is an explicit premise. There is no second eigenvalue, positivity or finite charge-space premise.

The charged_sector_ground_pair supplier and projectedGround_arbitrary_second start the induction on actual finite current words. The tail has lift gamma-1 and the opposite ground parity. Theta-sector source expansion and left linear closure then sum independent finite charge and oscillator supports; the three coefficient supports close by finite unions. Rank zero, zero projections, repeated sources, negative indices and indefinite forms are retained.

The result is an original twisted coefficient-law bridge on this actual tensor carrier. The entire requested Monster moonshine, VOA, CFT, symmetry anomaly, fusion, string theory, AdS/CFT and local-information-to-global-dynamics formalization remains the overarching objective. No completed physical model or literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_current_step`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.first_eigen_arbitrary_second`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/SourceToQ](../ChargedResidue/SourceToQ.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi](../NestedResidues/LatticeHalfFockCollisionJacobi.md)
