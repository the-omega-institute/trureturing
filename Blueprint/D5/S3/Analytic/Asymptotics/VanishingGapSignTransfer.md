# Sign transfer on meshes with vanishing gaps

## Abstract

Vanishing forward gaps let a mesh capture fixed positive excursions.

**Theorem 1.1 (Eventual interval hitting).**

Lean statement: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.eventually_hit_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.eventually_hit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If y tends to +∞ and its forward increments tend to zero, then for each ε>0 and natural K there is a real T such that every t≥T has a sample y(k) in [t,t+ε) with k≥K.

**Theorem 1.2 (Transfer positive excursions to negative samples).**

Lean statement: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.arbitrarily_late_negative_samples`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.arbitrarily_late_negative_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be uniformly continuous on ℝ. Suppose the real sequence y tends to +∞, its forward increments tend to zero, and a(k)+F(y(k)) tends to zero. If c>0 and every real T admits t≥T with F(t)≥3c, then every natural K admits k≥K with a(k)<−c. Use the uniform continuity radius at tolerance c in the interval-hitting theorem and take the sample far enough out that a(k)+F(y(k))<c.

**Theorem 1.3 (Logarithmic mesh from ratio one).**

Lean statement: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.log_mesh_of_ratio_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.log_mesh_of_ratio_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the real sequence x tends to +∞ and x(k+1)/x(k) tends to one, then log(x(k)) tends to +∞ and its forward increments tend to zero. Divergence gives eventual positivity, so the increments eventually equal log of the successive ratio.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.arbitrarily_late_negative_samples`
- Truth anchor: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.eventually_hit_interval`
- Truth anchor: `D5/S3/Analytic/Asymptotics/VanishingGapSignTransfer.log_mesh_of_ratio_one`
