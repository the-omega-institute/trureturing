# Actual original-source ground-current defect

## Abstract

Actual original-source ground-current defect

Write T(a,gamma)=physicalSlice(correctedField(a),gamma) and U(a,b,r)=mu(a,r,b) on the original source Carrier D. The target is the distinct ActualTensor D hu. NativeProduct(a,b,gamma,delta,r) is the complete-cutoff Q product of T(a,gamma) and T(b,delta). Defect is T(U(a,b,r),gamma+delta)-NativeProduct.

Actual physical locality supplies one order valid for every signed shift of the first slice. The accepted CurrentBorcherds.inverse_all supplies the native current inverse product for arbitrary original b and actual tensor input. Its proof retains the negative-insertion finite half-binomial triangle, the positive tail and the original source cutoff; no second inverse or jet-tail axiom is introduced.

For projected ground a and a0=h(i,0)a, the original source Jacobi commutator gives mu(a,r,h(i,d)b)=h(i,d)mu(a,r,b)-mu(a0,r+d,b). Its positive commutator terms vanish by the literal projected-ground source formula. Native Ward provides the same a0 on the actual tensor carrier. Combining this source equality with complete-product interchange proves the defect transport below.

CurrentDefectProduct is Q(J,Defect,1,d) with a fresh certified cutoff for the actual defect. Its bound includes the original source iterate and the intermediate product independently. Transport is unconditional, including all signed d, and keeps h0 and both projected signs. No RT premise, desired target module law, positivity or target vacuum is assumed.

**Theorem 1.1 (Native original-source defect transport).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect.projectedGround_defect_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect.projectedGround_defect_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, current i, charge alpha, projected sign epsilon, arbitrary original b and signed gamma, delta, r, d, Defect(a,h(i,d)b,gamma,delta+1,r)=CurrentDefectProduct(i,a,b,gamma,delta,r,d)-Defect(h(i,0)a,b,gamma+1,delta,r+d).

## References

- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect.projectedGround_defect_transport`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/Interchange](Interchange.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus](../LatticeActualStateFieldCalculus.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality](../LatticeHalfFockAllStatePhysicalLocality.md)
