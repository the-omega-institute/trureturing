# Lie radical transfer

## Abstract

Solvable extensions and actual radical quotients.

**Theorem 1.1 (A uniform two-step nilpotence bound).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (x : L), (\forall (y : L), (\forall (z : L), (\operatorname{lie}\left(x, \operatorname{lie}\left(y, z\right)\right) = 0))) \Rightarrow \operatorname{LieRing}.\operatorname{IsNilpotent}\left(L\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.nilpotent_of_triple_bracket_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every nested triple bracket vanishes, the actual lower central series vanishes at step two. This includes the zero algebra. The canonical proof is shared with the pointwise-stabilizer kernel and the full derivation-kernel construction.

**Theorem 1.2 (Solvable inverse images).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right)] \forall (I : \operatorname{LieIdeal}\left(k, M\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(I\right)] \operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieIdeal}.\operatorname{comap}\left(I, f\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.solvable_comap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Lie map with solvable kernel, the inverse image of a solvable ideal is solvable. Restrict the map to that inverse image and embed its kernel into the original solvable kernel. Surjectivity and finite dimensionality are not required.

**Theorem 1.3 (Simple ideals survive solvable kernels).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right)] \forall (I : \operatorname{LieIdeal}\left(k, L\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, I\right)] \operatorname{Function}.\operatorname{Injective}\left(\operatorname{LieHom}.\operatorname{comp}\left(f, \operatorname{LieIdeal}.\operatorname{incl}\left(I\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.injective_on_simple_ideal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restriction of any map with solvable kernel to an actual nonabelian simple ideal is injective. The restriction kernel embeds into the original solvable kernel; the simple ideal has trivial radical, so that restriction kernel vanishes.

**Definition 1.4 (A nonzero simple factor projection).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] [\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, M\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), (\operatorname{Function}.\operatorname{Surjective}\left(f\right) \Rightarrow \forall (I : \operatorname{LieIdeal}\left(k, L\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, I\right)] \exists x : I, f\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right) \ne 0 \Rightarrow \operatorname{LieEquiv}\left(k, I, M\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/LieRadicalTransfer.simpleIdealEquiv_of_surjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A surjective map onto a nonabelian simple Lie algebra restricts to a Lie equivalence on any nonabelian simple ideal with nonzero image. Surjectivity ensures its image is an actual target ideal. Its kernel vanishes by source simplicity and nonzero image, and its image is the full target by target simplicity.

**Theorem 1.5 (Simplicity under an actual equivalence).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] [\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, L\right)] \forall (e : \operatorname{LieEquiv}\left(k, L, M\right)), (\operatorname{LieAlgebra}.\operatorname{IsSimple}\left(k, M\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.isSimple_of_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual Lie equivalence transports the ideal dichotomy and nonabelian condition. The G2 exclusion uses this to transport simplicity from the actual hypothetical simple ideal to mathlib's actual Serre object.

**Theorem 1.6 (Solvable extensions).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), ([\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right)] [\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(M\right)] \operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(L\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.solvable_of_solvable_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Lie homomorphism over a field, a solvable kernel and a solvable codomain imply a solvable domain. The proof bounds the derived series of the domain first by the kernel and then by its own derived series. Surjectivity is not assumed.

**Theorem 1.7 (Identification of the actual radical).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] [\operatorname{IsNoetherian}\left(k, L\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), (\operatorname{Function}.\operatorname{Surjective}\left(f\right) \Rightarrow [\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right)] [\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, M\right)] \operatorname{LieHom}.\operatorname{ker}\left(f\right) = \operatorname{LieAlgebra}.\operatorname{radical}\left(k, L\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.kernel_eq_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Noetherian Lie algebra over a field, a surjective Lie map with solvable kernel and radical-free target has kernel equal to the actual solvable radical. The radical has solvable image under the surjection; that image must vanish. The reverse containment uses solvability of the kernel.

**Definition 1.8 (An actual quotient equivalence).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (M : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(M\right)] [\operatorname{LieAlgebra}\left(k, M\right)] [\operatorname{IsNoetherian}\left(k, L\right)] \forall (f : \operatorname{LieHom}\left(k, L, M\right)), (\operatorname{Function}.\operatorname{Surjective}\left(f\right) \Rightarrow [\operatorname{LieAlgebra}.\operatorname{IsSolvable}\left(\operatorname{LieHom}.\operatorname{ker}\left(f\right)\right)] [\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, M\right)] quotientEquiv : \operatorname{LieEquiv}\left(k, \operatorname{Quotient}\left(L, \operatorname{LieAlgebra}.\operatorname{radical}\left(k, L\right)\right), M\right)))))$$

*Formalization.* `D5/S3/QuadraticForms/LieRadicalTransfer.quotientEquiv_of_solvable_kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the same field, Lie algebra, Noetherian, surjectivity, solvable-kernel and trivial-target-radical hypotheses, the first isomorphism theorem gives an actual Lie equivalence from L modulo its actual radical to M. This conditional transfer lemma does not construct the required map for an evolution algebra.

**Theorem 1.9 (Separating radical-free quotients).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (L : \operatorname{Type}\left(\right)), ([\operatorname{LieRing}\left(L\right)] [\operatorname{LieAlgebra}\left(k, L\right)] \forall (aType : \operatorname{Type}\left(\right)), (\forall (H : aType \to \operatorname{Type}\left(\right)), ([\forall (a : aType), (\operatorname{LieRing}\left(H\left(a\right)\right))] [\forall (a : aType), (\operatorname{LieAlgebra}\left(k, H\left(a\right)\right))] [\forall (a : aType), (\operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, H\left(a\right)\right))] \forall (f : \forall (a : aType), (\operatorname{LieHom}\left(k, L, H\left(a\right)\right))), (\forall (a : aType), (\operatorname{Function}.\operatorname{Surjective}\left(f\left(a\right)\right)) \Rightarrow \left(\forall (x : L), (\forall (a : aType), (f\left(a, x\right) = 0) \Rightarrow x = 0) \Rightarrow \operatorname{LieAlgebra}.\operatorname{HasTrivialRadical}\left(k, L\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/LieRadicalTransfer.hasTrivialRadical_of_separating_surjections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A family of surjective Lie maps to radical-free targets makes L radical-free when their kernels have zero intersection, stated by the exact separating law on each x. The index type can be infinite or empty; no finite dimensionality is required. Every abelian ideal has zero image in every target and therefore vanishes. These are classical Lie facts supporting the Ma-then-Zhang credited KMV application, not a priority claim or a completed evolution-algebra classification.

## References

- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.hasTrivialRadical_of_separating_surjections`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.injective_on_simple_ideal`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.isSimple_of_equiv`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.kernel_eq_radical`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.nilpotent_of_triple_bracket_zero`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.quotientEquiv_of_solvable_kernel`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.simpleIdealEquiv_of_surjection`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.solvable_comap`
- Truth anchor: `D5/S3/QuadraticForms/LieRadicalTransfer.solvable_of_solvable_kernel`
