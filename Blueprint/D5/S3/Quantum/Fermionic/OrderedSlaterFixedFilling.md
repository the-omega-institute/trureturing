# Ordered Slater marginal spectra at fixed particle number

## Abstract

Ordered Slater marginal spectra at fixed particle number

**Theorem 1.1 (Compression after appending coordinate orbitals).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.retention_compression_of_canonical_columns`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.retention_compression_of_canonical_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any retained set I, let W consist of the original k columns of V followed by the coordinate columns for a finite set T in increasing site order. The retained compression of W is the compression of V plus the diagonal matrix that is one on retained sites belonging to T and zero on the other retained sites. Splitting the column sum isolates the contribution of the coordinate columns.

**Theorem 1.2 (Equal compression and distinct marginals at intermediate filling).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.alternating_fixed_filling_compression_twins`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.alternating_fixed_filling_compression_twins` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the cut contain four alternating sites, and let k range from two to the number of sites minus two. There exist two matrices V and W with k orthonormal columns whose retained compressions are equal. If d is the cardinality of the full retained occupation carrier, the ordered marginal of V has characteristic polynomial X to the power d minus two times the square of X minus one half. The corresponding marginal of W has polynomial X to the power d minus one times X minus one. Start with one orbital on each side of the four-site witness. For W replace the discarded orbital with a coordinate orbital. Append k minus two common coordinate orbitals outside the four sites. The occupation permutations and local signs preserve the two marginal polynomials, and the new columns add the same diagonal matrix to both retained compressions.

**Theorem 1.3 (The two fixed-filling criteria).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.fixed_filling_spectral_criteria`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.fixed_filling_spectral_criteria` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite ordered site type, a retained set I and a particle number k. The following condition is equivalent to each of two universal properties: there is at most one particle, there is at most one hole as expressed by the site count being at most k plus one, or the cut has no four alternating sites. The first universal property is that every orthonormal k-column orbital matrix has the complete product spectrum for the ordered marginal. The second is that every two such matrices with equal retained compressions have equal ordered marginal characteristic polynomials. For the forward implications, separated shuffle signs transport the grouped marginal to the ordered marginal and the ordered-prefix formula supplies each occupation weight. For the reverse implications the intermediate-filling matrices have identical compressions and distinct marginals. The polynomial distinction follows by evaluation at one.

**Theorem 1.4 (The full polynomial of a rank-one and coordinate projector sum).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.spectator_projector_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.spectator_projector_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T be a subset of a finite index type and let v be a normalized complex vector with zero entries on T. The sum of the rank-one matrix v times its adjoint and the coordinate projector on T has characteristic polynomial X to the power of the index count minus the cardinality of T minus one times X minus one to the power of the cardinality of T plus one. Reindex by T and its complement. The first block is the identity and the second is the rank-one matrix of the restricted vector, whose squared norm is one.

**Theorem 1.5 (The compression polynomial of the extended two-orbital witness).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.canonical_two_mode_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.canonical_two_mode_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the first of two orthonormal orbitals vanish on discarded sites and the second vanish on retained sites. For a finite set T of zero rows, let W have the two original columns followed by the coordinate columns for T in increasing order. Let t be the number of sites in T on the retained side and m the number of retained sites. The retained compression of W has characteristic polynomial X to the power m minus t minus one times X minus one to the power t plus one. The restricted first orbital has norm one and vanishes at every retained spectator site, so the coordinate-projector formula applies.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.alternating_fixed_filling_compression_twins`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.canonical_two_mode_compression`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.fixed_filling_spectral_criteria`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.retention_compression_of_canonical_columns`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterFixedFilling.spectator_projector_charpoly`
- Dependency: [D5/S3/Quantum/Fermionic/OrderedSlaterPrefix](OrderedSlaterPrefix.md)
- Dependency: [D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase](SlaterFixedFillingPhase.md)
- Dependency: [D5/S3/Quantum/Fermionic/SlaterSpectatorMinor](SlaterSpectatorMinor.md)
