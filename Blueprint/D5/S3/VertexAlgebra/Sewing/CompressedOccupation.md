# Absolute occupation summability for the literal compressed field

## Abstract

CompressedOccupation

The mathematical namespace is D5.S3.VertexAlgebra.CompressedOccupationSewing. D is arbitrary LatticeData; e is any natural, B any integral matrix Fin D.rank by Fin e, and C any integral e by e matrix with hC:forall i j,C i j=C j i and hCe:forall i,Even(C i i). Both ranks include zero. This module has NO hD or Gram positivity premise, either original or ambient. Its test p and the input oscillator polynomials are arbitrary. No positivity, nondegeneracy or complement restriction is added to the ambient data.

E abbreviates the actual ambient D e B C hC hCe. projectionMatrix D B is the complex matrix whose old-coordinate columns are delta(i,k) and whose external columns are the cast of the literal longitudinal D B i k, with Fin.addCases fixing the order. oldIndex sends (i,r) to (i.castAdd e,r), and oldOccupation is Finsupp.mapDomain of that exact map.

**Theorem 1.1 (projection_eq_linearSub).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projection_eq_linearSub`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projection_eq_linearSub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,e,B,C,hC,hCe, the actual polynomialProjection D B C hC hCe equals LongitudinalFockTranspose.linearSub (projectionMatrix D B). There is no Gram, test-state or matrix-rank hypothesis.

**Theorem 1.2 (oldOccupation_degree).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original occupation d has exactly the same unweighted degree after oldOccupation D B C hC hCe.

**Theorem 1.3 (oldOccupation_level).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_level`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original occupation d, its level in D equals the level of its literal old-coordinate injection in E. No positivity is needed.

**Theorem 1.4 (injection_basis).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.injection_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.injection_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original occupation d, polynomialInjection sends the native monomial b D d to b E (oldOccupation D B C hC hCe d). This states the actual monomial injection; it does not replace arbitrary polynomial states by a selected basis subset.

T a b' alpha beta u m v is defined to be the alpha+beta coefficient of compressed a b' (Finsupp.single alpha u) m (Finsupp.single beta v), with every a,b':Fin e→Int, every original integral alpha,beta, arbitrary oscillator polynomials u,v and every SIGNED m:Int. W is the d coefficient of polynomialProjection applied to the actual ambient wordMap at the lifted integral charges (alpha,a),(beta,b'), acting on the oldOccupation injection of f. omega is an arbitrary finite list of actual ambient oscillator indices.

**Theorem 1.5 (block_as_actual_projection).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_as_actual_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_as_actual_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,e,B,C,hC,hCe,a,b',alpha,beta,u,v,m, T equals polynomialProjection of canonical E at liftCharge a alpha and liftCharge b' beta, with the actual polynomial injections of u and v. Charge conservation is proved using the literal inclusion/projection. The original ambient cocycle remains inside canonical; it is not modified.

**Theorem 1.6 (block_coefficient_expansion).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_coefficient_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_coefficient_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any additional d:Occ D, coeff d (T a b' alpha beta u m v) equals sum over U in u.support and V in v.support of (u.coeff U * v.coeff V) times W at occurrences E (oldOccupation U), mode m, output d and input V. These are actual finite supports of the arbitrary input polynomials.

**Theorem 1.7 (projected_word_row_bound).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_row_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,e,B,C,hC,hCe,a,b',alpha,beta, there exists L:Real with 1 ≤ L such that for EVERY ambient descendant list omega there exists K:Nat, and for EVERY output d:Occ D there exists S:Real with 0 ≤ S, such that for ALL input f:Occ D and signed m:Int, norm(W omega m d f) ≤ S * rowWeight D L K f. L is chosen before omega; K before d; S may depend on d. The transpose support is finite here because that output occupation is fixed.

**Theorem 1.8 (projected_word_column_bound).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_column_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_column_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same full parameter scope there exists A:Real with 1 ≤ A such that for EVERY ambient omega there exists J:Nat, and for EVERY input f:Occ D there exists S:Real with 0 ≤ S, such that for ALL output d:Occ D and signed m:Int, norm(W omega m d f) ≤ S * columnWeight D A (J+f.degree) d. Here A is chosen before omega and f, and the output occupation is unrestricted. The transpose mass and energy theorems control its entire growing transpose support, with the original factorial denominator.

term a b' c alpha beta gamma u v w p r s q d is exactly q^(level D d) * H D p (T a (b'+c) alpha (beta+gamma) u (r+level D d) (b D d)) * H D (b D d) (T b' c beta gamma v (s-level D d) w) / weight(d). Level is cast to Int inside the two modes. H is the native factorial form, conjugate linear in its first slot and linear in its second; the inner coordinate is not conjugated. r and s are arbitrary signed integers, independent of d.

**Theorem 1.9 (compressed_sewing_summable).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.compressed_sewing_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.compressed_sewing_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,e,B,C,hC,hCe, every external a,b',c and original alpha,beta,gamma, ALL oscillator polynomials u,v,w,p, EVERY r,s:Int, and q:Complex with the sole extra premise hq:norm(q)<1, the function d ↦ norm(term ... r s q d) over EVERY original occupation d is Summable. There are no homogeneity, finite intermediate cutoff, original or ambient positivity, nonzero, invariant-pairing or completed-state hypotheses. This conclusion is absolute scalar occupation summability throughout the open unit disk.

Private W_transpose is the exact factorial coefficient-transpose formula for W, including both weights and the starred transpose coefficient. Private factorialEnvelope_as_radius and projection_column_transport retain the frequency denominator and cancel the actual factorial weight. Private projected_word_contraction_summable allows arbitrary occupation-dependent signed mode functions m,n before the public fixed-offset theorem. Private block_basis_expansion and term_expansion are consumed finite polynomial expansions, retaining exactly one star on p.coeff P. These six helpers stay private. Public definitions/abbreviations are E, projectionMatrix, oldIndex, oldOccupation, T, W and term; the nine public theorems are precisely the Describe entries here. Imported private CanonicalOccupation and CanonicalOccupationRow suppliers are opened explicitly in the unchanged source.

The proof consumes the ambient row and column estimates and polynomial_factorialEnvelope_summable, then the actual projection transpose, finite polynomial expansions and a norm bound. It does not invoke ambient occupation sewing as a premise. Its term is later consumed literally by ActualCompressedOccupationProduct. Provenance is the final native CompressedOccupation.lean export, SHA256 969e9b20dbc3c8434530097e8d2f90343215bf829fd3d4c6a55d70295037dc7d. CanonicalOccupation, LatticeCosetCompression and LongitudinalFockTranspose retain their original attribution and definitions. All import-to-EOF comments, private openings, headers and proofs are byte exact. Its I metadata follows the actual CanonicalOccupation and LatticeCosetCompression dependencies; it does not restrict the mathematical telescope. The incomplete source-bound escape audit is disclosed at https://github.com/the-omega-institute/trureturing/issues/29344. Typed escape registration is a separate obligation; no braid/category/CFT or string completion is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_as_actual_projection`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.block_coefficient_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.compressed_sewing_summable`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.injection_basis`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.oldOccupation_level`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_column_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projected_word_row_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CompressedOccupation.projection_eq_linearSub`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression](../Sectors/LatticeCosetCompression.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupation](CanonicalOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/LongitudinalFockTranspose](LongitudinalFockTranspose.md)
