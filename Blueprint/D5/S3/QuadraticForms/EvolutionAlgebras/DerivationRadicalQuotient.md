# Arbitrary zero-annihilator derivations

## Abstract

The radical quotient of zero-annihilator evolution derivations.

**Theorem 1.1 (Actual solvable-radical quotient).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(mu\right)) \Rightarrow ((\operatorname{LinearMap}.\operatorname{ker}\left(mu\right) = \operatorname{bot}\left(\right)) \Rightarrow (\exists (r : \operatorname{Nat}\left(\right)), (\exists (m : \operatorname{Fin}\left(r\right) \to \operatorname{Nat}\left(\right)), ((\forall (a : \operatorname{Fin}\left(r\right)), (3 \le m\left(a\right))) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, \operatorname{Quotient}\left(\operatorname{derivations}\left(mu\right), \operatorname{LieAlgebra}.\operatorname{radical}\left(k, \operatorname{derivations}\left(mu\right)\right)\right), \operatorname{DirectSum}\left(\operatorname{Fin}\left(r\right), (fun a \mapsto \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\left(a\right)\right), k\right))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any algebraically closed field of characteristic zero and let V be finite-dimensional. For any bilinear commutative evolution multiplication with an actual natural basis and zero annihilator, the actual derivation Lie algebra modulo its actual solvable radical is Lie equivalent to a finite direct sum of standard orthogonal Lie algebras with all sizes at least three. The sum may be empty, including when V is zero. No unit, associativity, perfectness, square-dimension or semisimplicity assumption is imposed. The construction uses the scalar-corrected actions on the nondegenerate reductions of the orthogonal complements of the block spans. The general stabilizer surjections have kernels with zero triple brackets; their preimage together with the abelian diagonal part is solvable. The discarded factors of dimensions zero and one vanish and the dimension-two factor is abelian. All retained factors have trivial radical, including the actual split dimension-four case. The first isomorphism theorem therefore identifies the kernel with the actual radical and gives the displayed quotient. This is the quotient part of Corollary 8 of the supplied note by Haobo Ma, then Wenlin Zhang. Orthogonal structure and the radical facts are classical. The actual simple-ideal classification and the literal Serre G2 exclusion are stated separately below.

**Theorem 1.2 (Every actual nonabelian simple ideal).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(mu\right)) \Rightarrow ((\operatorname{LinearMap}.\operatorname{ker}\left(mu\right) = \operatorname{bot}\left(\right)) \Rightarrow (\forall (I : \operatorname{LieIdeal}\left(k, \operatorname{derivations}\left(mu\right)\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, I\right)] \exists (m : \operatorname{Nat}\left(\right)), ((m = 3 \lor 5 \le m) \land (\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, I, \operatorname{LieAlgebra}.\operatorname{Orthogonal}.\operatorname{so}\left(\operatorname{Fin}\left(m\right), k\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual nonabelian simple Lie ideal of the actual derivation algebra is Lie equivalent to standard so3 or to so_m for m at least five. A solvable kernel cannot contain a nonzero simple ideal. A nonzero coordinate projection has ideal image because the full map is surjective; simplicity of the coordinate then gives the equivalence. If that coordinate has size four, the proved actual so4 equivalence with so3 times so3 supplies a nonzero size-three projection. This concerns ideals, not arbitrary subalgebras or faithful actions.

**Theorem 1.3 (Exclusion of actual sl3).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(mu\right)) \Rightarrow ((\operatorname{LinearMap}.\operatorname{ker}\left(mu\right) = \operatorname{bot}\left(\right)) \Rightarrow (\forall (I : \operatorname{LieIdeal}\left(k, \operatorname{derivations}\left(mu\right)\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, I\right)] \neg\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, I, \operatorname{SpecialLinear}.\operatorname{sl}\left(\operatorname{Fin}\left(3\right), k\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_not_sl3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No such simple ideal is Lie equivalent to the actual standard special linear algebra sl3. Its proved dimension eight is not m choose two for any m. The simple-ideal type theorem supplies an actual orthogonal equivalence before the dimension argument.

**Theorem 1.4 (Exclusion of the actual Serre G2).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] [\operatorname{IsAlgClosed}\left(k\right)] [\operatorname{CharZero}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), ((\operatorname{IsEvolutionAlgebra}\left(mu\right)) \Rightarrow ((\operatorname{LinearMap}.\operatorname{ker}\left(mu\right) = \operatorname{bot}\left(\right)) \Rightarrow (\forall (I : \operatorname{LieIdeal}\left(k, \operatorname{derivations}\left(mu\right)\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, I\right)] \neg\operatorname{Nonempty}\left(\operatorname{LieEquiv}\left(k, I, \operatorname{LieAlgebra}.\operatorname{g}_{2}\left(k\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_not_g2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target is literally mathlib's LieAlgebra.g₂ k, defined by the G2 Cartan matrix and Serre relations. The companion SerreG2MatrixImage source constructs a surjection from this actual object to a proved fourteen-dimensional matrix image. A hypothetical ideal equivalence transports simplicity to the Serre object, so its nonzero surjection is injective and gives a proved correspondence. Fourteen is not m choose two. No unconditional Serre dimension theorem, assumed equivalence or dimension-tagged proxy is used.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.result`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_not_g2`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_not_sl3`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient.simple_ideal_type`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation](AlgebraicGroupRealizationRefutation.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalLieStructure](../OrthogonalLieStructure.md)
- Dependency: [D5/S3/QuadraticForms/SerreG2MatrixImage](../SerreG2MatrixImage.md)
