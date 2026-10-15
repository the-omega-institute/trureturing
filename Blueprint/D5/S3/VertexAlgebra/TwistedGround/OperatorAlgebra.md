# The Actual Finite Twisted-Ground Operator Algebra

## Abstract

The original twisted ground representation has a charge-indexed full endomorphism basis, exact trace coefficients and scalar commutant.

Let D be an arbitrary finite-rank even integral lattice whose Gram determinant is a unit. Keep the original lower-triangular cocycle, sign extension E, reflection-generated subgroup K and quotient E/K. For a mod-two charge v, its integral lift is a_v(i)=Int.ofNat(v(i).val), literally zero or one in every coordinate. The canonical group element is g_v=[(0,a_v)]. For an actual representation rho on Ground(n), write A_v=rho(g_v) and D_v=rho(g_v inverse). The dual is the image of the actual inverse group element, not a sign-free lift or an assumed complex adjoint.

**Theorem 1.1 (Trace duality, complete basis, reconstruction and commutant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.actual_operator_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.actual_operator_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume rank(D)=n+n and that the original negative central sign acts as minus the identity. These are the only representation hypotheses: no irreducibility, spanning assertion or trace formula is assumed. The supplied nondegenerate mod-two Gram pairing gives, for every nonzero reduced charge, a partner with pairing one. The original quotient commutation law therefore gives an anticommuting invertible operator. Conjugation changes the given operator to its negative, while cyclic finite trace preserves its trace. Over the complex field this forces trace zero.

The reduced charge of g_v inverse times g_w is -v+w. If v differs from w it is nonzero, so tr(D_v A_w)=0. If v=w the group product is exactly the identity, so its trace is d=dim_C Ground(n)=2^n. Thus tr(D_v A_w)=d times the Kronecker delta. Division by d is legitimate because a finite function space on (Fin(n) to Z/2) has positive dimension, also when n=0.

Applying d inverse times tr(D_v times -) to a vanishing finite linear combination isolates its v coefficient. Consequently the A_v are linearly independent. There are 2^rank(D)=2^(n+n) such operators, exactly dim_C End_C Ground(n)=(2^n)^2. They form an actual Basis of the entire complex endomorphism space. For every endomorphism T, its v coordinate is d inverse times tr(D_v T), and T=sum_v (d inverse times tr(D_v T)) A_v. The sum ranges over the finite type of all mod-two charges, and the coordinates are the finitely supported coordinates of this basis.

If T commutes with all A_v, finite reconstruction makes it commute with every endomorphism. Mathlib's free-module center theorem, Module.End.mem_center_iff, then identifies T as a complex scalar identity. That theorem tests commuting endomorphisms against rank-one coordinate maps. Conversely every complex scalar identity commutes with all A_v. This conclusion uses the complete operator span, not an application of the previously proved irreducibility.

**Definition 1.2 (The literal chosen native representation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.nativeOperatorAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.nativeOperatorAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take n to be Classical.choose(actual_twisted_ground_representation D hu), and rho to be Classical.choose(Classical.choose_spec(actual_twisted_ground_representation D hu)). The transparent operands chosenRank and chosenRepresentation denote these exact expressions; the carrier remains Ground(n), with no new carrier or scalar field. The second choose_spec supplies rank(D)=n+n and the negative central action for exactly that rho. The universal construction gives its basis, trace coefficients, reconstruction and scalar commutant on Ground(n) itself. No equality with a displayed quotientRepresentation witness is used. These literal expressions match groundRank, ActualGround and groundRepresentation in the native charged-tensor interface. A module-alias binding to that interface is separate from the literal-choice result.

At rank zero the sole charge operator is the identity on the one-dimensional ground space, its trace dual coefficient is ordinary trace, and the same reconstruction and commutant formulas hold. No rank-24 specialization, signature restriction, occupation cutoff or numerical enumeration is needed. This is the finite ground operator algebra only. It does not prove twisted Jacobi, realized VOA fusion rules, orbifold extension, a Monster action, a full string construction or an AdS/CFT correspondence.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.actual_operator_algebra`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra.nativeOperatorAlgebra`
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../LatticeTwistedGroundRealization.md)
