# Original-Side Fragment Mesh Error

## Abstract

Localize actual fragment mesh errors on the original mass, then separate unconditional probability reductions from the remaining scalar perpetuity identity.

**Theorem 1.1 (A positive boundary witnessed by the original mass).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.original_mesh_boundary_witness`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.original_mesh_boundary_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative retained mass x and deletion d, positive mesh width h, d smaller than delta, original mass x+d at most R, and different natural floor indices, there exists a natural k between 1 and floor(R/h). The original mass belongs to [kh,kh+delta). The witness is floor(x/h)+1. Floor monotonicity places the new mass above this boundary, while the strict upper bound on x and on d places it below kh+delta. No restriction delta<h is imposed.

**Theorem 1.2 (An unconditional finite boundary reduction).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_original_boundary_probability`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_original_boundary_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual fragmentLaw with positive zeta, nonnegative epsilon, positive delta and h, and any real R, the probability of a changed mesh index with total mass at most R is bounded by ofReal(min(epsilon,zeta))/ofReal(delta), plus the sum of original-mass interval probabilities over k in [1,floor(R/h)]. The existing retained/deleted partition and deletion tail are consumed directly. Neither a density nor a distributional fixed point is a hypothesis of this reduction.

**Theorem 1.3 (The exact remaining distributional hypothesis).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mass_interval_of_perpetuity`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mass_interval_of_perpetuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar mass law is explicitly the pushforward of the existing fragmentLaw by c mapped to c.mass. Assuming this very pushforward equals its uniformScaleMixture, its probability of [x,x+delta) is at most ofReal(delta/zeta). Probability normalization and nonnegative support are derived from the actual finite-measure carrier. The perpetuity equality itself is not proved in this module and is not replaced by a new axiom.

**Theorem 1.4 (An explicit finite-window estimate).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_window_of_perpetuity`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_window_of_perpetuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same scalar perpetuity equality, the actual windowed mesh-error probability is at most ofReal(min(epsilon,zeta))/ofReal(delta) plus floor(R/h) times ofReal(delta/zeta). The finite union is indexed by positive boundaries only. When floor(R/h) is zero its contribution is zero. All positivity assumptions and the full distributional equality remain in the Lean signature.

**Theorem 1.5 (An unconditional bound outside the mass window).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_total_mass_tail`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_total_mass_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive zeta and R, the probability that the original total mass is at least R is at most ofReal(zeta)/ofReal(R). The proof obtains the actual total-mass first moment by applying the existing fragment-law integral theorem to the constant test function one, then reuses Markov's inequality. There is no perpetuity, independence or anti-concentration premise here.

**Theorem 1.6 (A full-space mesh estimate).**

Lean statement: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_global_of_perpetuity`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_global_of_perpetuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive R as well as the finite-window assumptions, split the actual mesh-error event into total mass at least R and the windowed event. The resulting bound is zeta/R plus min(epsilon,zeta)/delta plus floor(R/h)*delta/zeta, represented in extended nonnegative reals. The scalar perpetuity equality remains an explicit hypothesis. This statement does not certify any of the original 152 trial-integral inequalities.

The retained fragment measure can have an atom at zero. Applying the interval bound to the original total mass is therefore a substantive choice. The scalar dyadic-Poisson/perpetuity identification is still an independent formalization obligation. No Lean kernel, axiom-closure or Scribe-emission success follows from the presence of these source files or their declaration handles.

## References

- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mass_interval_of_perpetuity`
- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_global_of_perpetuity`
- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_original_boundary_probability`
- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_mesh_window_of_perpetuity`
- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.fragment_total_mass_tail`
- Truth anchor: `D5/S3/PrimeGaps/FragmentOriginalMesh.original_mesh_boundary_witness`
- Dependency: [D5/S3/PrimeGaps/FragmentMeshTruncation](FragmentMeshTruncation.md)
- Dependency: [D5/S3/PrimeGaps/FragmentUniformSmoothing](FragmentUniformSmoothing.md)
