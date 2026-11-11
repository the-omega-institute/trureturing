# A Noncyclic Norm and Splitting Counterexample

## Abstract

A bijective native coinvariant norm does not force a compatible abelian-kernel extension to split.

Write Dn for Mathlib's DihedralGroup n, of order 2n. Its rotations are r(i) and its reflections are sr(i), with indices in ZMod n. The counterexample uses the sign representation of D3 on the nonzero additive module F3=ZMod 3 and the exact extension 1 to C3 to D9 to D3 to 1. The kernel C3 is Multiplicative F3. Reflections act by inversion, so this is an abelian kernel with nontrivial conjugation action.

**Theorem 1.1 (The norm and extension belong to the same specimen).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.noncyclic_norm_splitting_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.noncyclic_norm_splitting_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist rho : Representation (ZMod 3) (DihedralGroup 3) (ZMod 3), S : GroupExtension (Multiplicative (ZMod 3)) (DihedralGroup 9) (DihedralGroup 3), and an additive equivalence iota : Additive (Multiplicative (ZMod 3)) equiv+ ZMod 3 with all six properties: for every i and a in ZMod 3, rho(r(i))(a)=a; for every such i and a, rho(sr(i))(a)=-a; DihedralGroup 3 is not cyclic; SemilinearKernelNorm.coinvariantsNorm rho is bijective; for every e : DihedralGroup 9 and a : Additive (Multiplicative (ZMod 3)), iota(Additive.ofMul(S.conjAct e a.toMul))=rho(S.rightHom e)(iota(a)); and S.Splitting is empty.

An invariant vector is fixed by a reflection, hence satisfies -a=a and is zero in F3. Every vector is also a generator difference: rho(sr(0))(a)-a=-a-a=a in F3. Thus the native coinvariant quotient and invariant submodule both have only their zero element. The actual unnormalized quotient norm is therefore bijective. This gives no injectivity statement for the zero norm on the original nonzero module F3.

The projection D9 to D3 reduces rotation indices modulo three and preserves the rotation or reflection tag. The kernel inclusion sends a to r(3a), with a represented by 0, 1 or 2. Its image consists exactly of r(0), r(3), r(6), proving native exactness. The additive equivalence iota removes the Additive and Multiplicative tags. Conjugation by a rotation fixes this kernel, while conjugation by a reflection negates its index. Injectivity of the inclusion transfers this calculation to S.conjAct, giving precisely the same sign action as rho.

Every lift of r(1) in D3 is a rotation with index 1, 4 or 7 in ZMod 9. Its cube is r(3), which differs from the identity. A homomorphic section would preserve the equation r(1)^3=1 in D3 and is therefore impossible. Only the residue identities and these three lift indices are decided; no enumeration of sections is used. The construction and obstruction are derived here using the native Mathlib interfaces; no literature novelty is claimed.

**Definition 1.2 (The precise unrestricted implication).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.claim`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition claim quantifies over R, G, V, N, E : Type, with R a commutative ring, G a group with Fintype G, V an additive commutative group and R-module, N a commutative group, and E a group. For every rho : Representation R G V, S : GroupExtension N E G and additive equivalence iota : Additive N equiv+ V, it asserts that bijectivity of SemilinearKernelNorm.coinvariantsNorm rho, together with the equation iota(Additive.ofMul(S.conjAct e a.toMul))=rho(S.rightHom e)(iota(a)) for every e : E and a : Additive N, implies Nonempty S.Splitting. The proposed implication has no cyclicity, trace-one or projectivity hypothesis.

**Theorem 1.3 (The unrestricted implication is false).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem result has conclusion Not claim. Instantiate claim at R=V=ZMod 3, G=DihedralGroup 3, N=Multiplicative (ZMod 3) and E=DihedralGroup 9. Apply it to the representation, extension and additive equivalence supplied together by the counterexample. Its norm bijectivity and conjugation equation would produce a splitting of that very extension, contradicting its nonsplitting. Thus bijectivity of the native coinvariant norm alone is insufficient for general finite base groups, even with a finite nontrivial abelian kernel and the correct compatible action. This does not refute a cyclic-group splitting theorem or any theorem with additional hypotheses.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.claim`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.noncyclic_norm_splitting_counterexample`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/NoncyclicNormSplittingCounterexample.result`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SemilinearKernelNorm](SemilinearKernelNorm.md)
