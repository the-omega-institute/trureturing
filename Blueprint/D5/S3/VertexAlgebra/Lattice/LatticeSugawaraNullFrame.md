# LatticeSugawaraNullFrame

## Abstract

LatticeSugawaraNullFrame

Original quadratic Sugawara finite change of basis on the unchanged integral-charge polynomial matter carrier, using an arbitrary finite transverse basis of an actual null frame. The coefficient matrix is computed from the original inverse Gram matrix and both actual basis representations. Both inverse-Gram equations are hypotheses. The plus-plus, minus-minus and longitudinal-transverse coefficients cancel; both cross terms survive. The actual normal-order branch is preserved for every integer pair. This does not replace the transverse block by an assumed inverse metric. The original state-dependent finite capture is regrouped exactly. These are repository mathematical derivations, not empirical conformal field theory or a new model.

Full BRST matter-mode capture and assembly into Q minus d0, relative b0 and total-L0 zero-mode cancellation, preservation and bounds of the literal physical shell, full h delta strict raising, rank-26 nilpotence, HPL, cohomology, no-ghost, true Vnatural, strings and AdS/CFT remain unproved here. Original shell59141 is not imported or assumed. Native compilation proves only the exact Lean statements. Earlier provider audit limitations are linked at https://github.com/the-omega-institute/trureturing/issues/25604. That issue preserves all 39 original quartet obligations and names all 107 current retained filtration/Sugawara targets with exact canonical statement, source, type and binding identities: 146 unique unfinished audits, zero declared_validated. All seven original-family/source-selection, reconstruction, realization, whole-family variation, role/anchor sensitivity and observational-dependence evidence gaps remain unresolved. New registrations carry whole-theorem bridges but assertion-valued diagnostic attempts lack faithful operand selection and reconstruction. No declared_validated status, escape certificate or admission is claimed; actual unclassified diagnostics are collected in the scoped report for root review.

**Theorem 1.1 (a_standardBasis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_standardBasis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_standardBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (i : Fin D.rank) (n : ℤ) : a (standardBasis D i) n = neutralMode D i n

**Theorem 1.2 (a_basis_expand).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_basis_expand`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_basis_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E D)) (u : E D) (n : ℤ) : a u n = ∑ c : ι, b.repr u c • a (b c) n

**Theorem 1.3 (originalNormal_eq_normalSummand).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_eq_normalSummand`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_eq_normalSummand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (i j : Fin D.rank) (k l : ℤ) : originalNormal (standardBasis D i) (standardBasis D j) k l = normalSummand D i j k l

**Theorem 1.4 (originalNormal_basis_expand).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_basis_expand`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_basis_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E D)) (u v : E D) (k l : ℤ) : originalNormal u v k l = ∑ c : ι, ∑ d : ι, (b.repr u c * b.repr v d) • originalNormal (b c) (b d) k l

**Theorem 1.5 (weighted_normal_frame).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_normal_frame`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_normal_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k l : ℤ) : (∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j • normalSummand D i j k l) = ∑ c : Label t, ∑ d : Label t, frameCoeff F B H c d • frameNormal F B c d k l

**Theorem 1.6 (frameCoeff_plus_plus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : frameCoeff F B H (plus t) (plus t) = inverseGramPair H F.eMinus F.eMinus

**Theorem 1.7 (frameCoeff_minus_minus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_minus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : frameCoeff F B H (minus t) (minus t) = inverseGramPair H F.ePlus F.ePlus

**Theorem 1.8 (frameCoeff_plus_minus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_minus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : frameCoeff F B H (plus t) (minus t) = inverseGramPair H F.eMinus F.ePlus

**Theorem 1.9 (frameCoeff_minus_plus).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_plus`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : frameCoeff F B H (minus t) (plus t) = inverseGramPair H F.ePlus F.eMinus

**Theorem 1.10 (inverseGram_symmetric).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.inverseGram_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.inverseGram_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) : H = H.transpose

**Theorem 1.11 (weighted_frame_sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_frame_sector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_frame_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source declaration (implicit section variables are retained by the native full-telescope Reg bridge): (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (k l : ℤ) : (∑ c : Label t, ∑ d : Label t, frameCoeff F B H c d • frameNormal F B c d k l) = frameNormal F B (plus t) (minus t) k l + frameNormal F B (minus t) (plus t) k l + ∑ r : Fin t, ∑ s : Fin t, frameCoeff F B H (transverse t r) (transverse t s) • frameNormal F B (transverse t r) (transverse t s) k l

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_basis_expand`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.a_standardBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_minus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_minus_plus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_minus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.frameCoeff_plus_plus`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.inverseGram_symmetric`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_basis_expand`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.originalNormal_eq_normalSummand`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_frame_sector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame.weighted_normal_frame`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration](LatticeBRSTModeFiltration.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates](LatticeLightConeCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](../LatticeSugawaraCurrents.md)
