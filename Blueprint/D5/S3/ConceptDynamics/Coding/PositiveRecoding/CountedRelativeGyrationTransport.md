# Transport forward orbit phases under timed history equivalences

## Abstract

Transport forward orbit phases under timed history equivalences.

TimedEquiv A B consists of an equivalence of actual legal two-sided paths and its law for every signed integer translation. It induces the retained primitive-path and orbit-quotient equivalences. basisEquiv expresses the orbit bijection in the existing least-word PathBasis. offsetFin is the canonical target forward offset, offset its ZMod d value, and phaseInteger its nonnegative Fin representative in the integers.

offset_comp keeps the source canonical representative fixed and identifies phases by uniqueness below minimal period, including signed-time Euclidean reduction. Summing and reindexing by basisEquiv gives gyration_comp. gyration_basis_change retains both endpoint terms; gyration_conjugate cancels them only with the same chart. elementary uses the original elementaryHomeomorph and gyration_elementary recovers relativeForwardGyration. timeEquiv A s has gyration equal to the number of actual primitive d-orbits times the signed class of s. General transport laws use all nonzero periods, without imposing divisibility by three or nonemptiness. Agreement only on orbit permutations is insufficient for offset_congr or gyration_congr: both require equality on all actual primitive images.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (orbitEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.orbitEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.orbitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Descend the time-equivariant primitive-path equivalence to the actual orbit quotients at each nonzero period. This transports orbit classes before choosing canonical representatives.

**Definition 1.2 (basisEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly the actual orbit bijection, expressed in the supplier's finite canonical bases. Its target is not chosen independently of the actual map.

**Theorem 1.3 (offset_comp).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_comp`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward offset of a composite is the first offset plus the second offset at the transported canonical basis path. Phase uniqueness controls the sum modulo the period.

**Remark 1.4 (TimedEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.TimedEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.TimedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A genuine equivalence of the two actual legal-history carriers, with the literal integer-time law. This packages equivariance, never a gyration identity.

**Remark 1.5 (refl).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.refl`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.refl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity path equivalence preserves every integer translation. It is the identity object for the transport and gyration laws.

**Remark 1.6 (comp).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.comp`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.comp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the actual path equivalences and their signed-time laws in traversal order. The intermediate counted graph is retained.

**Remark 1.7 (symm).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.symm`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.symm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Invert the path equivalence and derive its signed-time law from bijectivity. This gives reverse transport on the same histories.

**Remark 1.8 (ext).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.ext`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.ext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pointwise equality of the underlying path maps determines a TimedEquiv. The time-law proof contributes no additional choice.

**Remark 1.9 (semiconj).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.semiconj`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.semiconj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer-time law at one gives semiconjugacy of the actual forward shifts. This connects time-equivariant maps to the existing periodic-point API.

**Remark 1.10 (minimalPeriod).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.minimalPeriod`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.minimalPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A time-equivariant equivalence preserves the least period of every path. Applying the forward and inverse maps gives equality rather than only divisibility.

**Remark 1.11 (primitiveEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict to paths whose least period is exactly d. This is the primitive stratum used in the orbit and phase construction.

**Remark 1.12 (primitiveEquiv_congr).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv_congr`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv_congr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Agreement on the actual primitive histories gives equality of their primitive images, including the original target history, by subtype extensionality.

**Remark 1.13 (sameOrbit_iff).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.sameOrbit_iff`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.sameOrbit_iff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two primitive paths lie in the same shift orbit exactly when their images do. The forward and inverse time laws justify descent to orbit quotients.

**Remark 1.14 (basisEquiv_apply).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_apply`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The induced basis map chooses the existing canonical representative of the transported primitive path. It does not choose a new orbit ordering.

**Remark 1.15 (basisEquiv_comp).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_comp`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_comp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Canonical basis transport respects composition. This is the reindexing identity used when summing composite offsets.

**Remark 1.16 (offsetFin).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offsetFin`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offsetFin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the unique forward offset below d from the target canonical representative to the actual image path. Primitivity and nonzero d control uniqueness.

**Remark 1.17 (offset).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the canonical forward offset in ZMod d. Reduction retains the phase even when the induced orbit permutation is unchanged.

**Remark 1.18 (offset_congr).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_congr`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_congr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both offsets use the identical canonical SOURCE basis representative. Equality of the actual primitive target images identifies their canonical forward offsets; equality of orbit permutations alone would not suffice.

**Remark 1.19 (phaseInteger).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phaseInteger`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phaseInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Interpret the canonical Fin offset as a nonnegative integer. This is the signed-time representative used in the literal history equation.

**Remark 1.20 (phase_equation).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phase_equation`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phase_equation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual image path is the transported canonical representative translated by its forward phase. This relates the finite offset to the full integer-indexed history.

**Remark 1.21 (finEquiv_timeIndex).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.finEquiv_timeIndex`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.finEquiv_timeIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reduce an arbitrary SIGNED integer, using Euclidean blockAddress, not a homomorphism from all rationals or an unstated orientation convention.

**Remark 1.22 (gyration).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the forward offsets over the existing finite canonical primitive basis. Empty primitive strata contribute the empty sum.

**Remark 1.23 (gyration_congr).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_congr`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_congr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original forward-offset sum depends only on the map on actual primitive d histories. The finite canonical source basis is the same in both sums.

**Remark 1.24 (gyration_comp).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_comp`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_comp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum offset_comp and reindex by the transported basis equivalence. The resulting gyration is additive under composition for every nonzero period.

**Remark 1.25 (gyration_refl).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_refl`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_refl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity map has zero forward offset on each canonical primitive path, so its total gyration is zero.

**Remark 1.26 (gyration_symm).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_symm`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_symm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply additivity to a map and its inverse. The inverse gyration is the additive negative of the original value.

**Remark 1.27 (gyration_basis_change).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_basis_change`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_basis_change` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Basis changes telescope, including both endpoint terms. For a loop the same actual chart is used at both ends, so its two terms cancel.

**Remark 1.28 (gyration_conjugate).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_conjugate`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_conjugate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two contributions of the same change of path coordinates cancel around a loop. This proves conjugacy invariance of the total gyration.

**Remark 1.29 (elementary).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.elementary`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.elementary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite automorphisms may rotate an orbit: no relabeling-zero rule occurs.

**Remark 1.30 (gyration_elementary).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_elementary`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_elementary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the existing elementary RS-to-SR homeomorphism, the transport sum is exactly relativeForwardGyration. Both use the original ranked primitive paths.

**Remark 1.31 (timeEquiv).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.timeEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.timeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translate every history by the signed integer s. Translation is a time-equivariant automorphism of the same counted graph.

**Remark 1.32 (basisEquiv_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Time translation preserves each primitive orbit and hence its canonical basis representative. Its nontrivial contribution lies in the phase.

**Remark 1.33 (offset_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On every canonical primitive d-path, signed translation by s has forward offset equal to s modulo d.

**Remark 1.34 (gyration_time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_time`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_time` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every primitive orbit contributes the same signed offset s. Summing gives the actual primitive-orbit cardinality multiplied by s in ZMod d.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.TimedEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_apply`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_comp`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.basisEquiv_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.comp`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.elementary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.ext`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.finEquiv_timeIndex`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_basis_change`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_comp`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_congr`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_conjugate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_elementary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_refl`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_symm`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.gyration_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.minimalPeriod`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offsetFin`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_comp`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_congr`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.offset_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.orbitEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phaseInteger`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.phase_equation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.primitiveEquiv_congr`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.refl`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.sameOrbit_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.semiconj`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.symm`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/CountedRelativeGyrationTransport.timeEquiv`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration](../CountedOriginalOrbitGyration.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree](../CountedPositiveTriangleModThree.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerTranslation](SplitTowerTranslation.md)
