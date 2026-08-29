# Jet Resolvent Semisimplification

## Abstract

A finite nilpotent jet pencil reduces to one simple pole carrying its length as weight.

**Theorem 1.1 (Trace and logarithmic derivative retain only jet multiplicity).**

$$\forall m \in \mathbb{N}, rho \in \mathbb{C}, s \in \mathbb{C},\; \left(0 < m \land s \ne rho\right) \Rightarrow \left(\operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, s\right)^{-1}\right) = \frac{m}{s - rho} \land \left(\operatorname{logDeriv}\left((z \mapsto \operatorname{det}\left(\operatorname{jetPencil}\left(m, rho, z\right)\right)), s\right) = \frac{m}{s - rho} \land \left(\operatorname{MeromorphicAt}\left((z \mapsto \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), rho\right) \land \left(\operatorname{meromorphicOrderAt}\left((z \mapsto \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), rho\right) = -1 \land \operatorname{Tendsto}\left((z \mapsto {z - rho} \times \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), \operatorname{nhdsWithin}\left(rho, \mathbb{C} \setminus \{rho\}\right), \operatorname{nhds}\left(m\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For length m, nilpotentJetShift has value one exactly one step below the diagonal and zero elsewhere. The named jetPencil is (s-rho) times the identity minus that shift.

The theorem assumes positive length, so the jet is nonempty and its weight is nonzero. The excluded length-zero pencil has determinant one and trace resolvent zero, and therefore has no pole. The separate premise s != rho is exactly the pointwise invertibility domain for a positive-length pencil.

Lower triangularity makes the pencil determinant (s-rho)^m and every diagonal inverse entry (s-rho)^(-1). Summing the diagonal and differentiating the determinant give the two displayed identities. The punctured identity also proves that the trace resolvent is meromorphic with order minus one and that multiplication by s-rho converges to the nonzero residue m.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification`
