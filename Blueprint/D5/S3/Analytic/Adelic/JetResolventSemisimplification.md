# Jet Resolvent Semisimplification

## Abstract

A finite nilpotent jet pencil reduces to one simple pole carrying its length as weight.

**Theorem 1.1 (Trace and logarithmic derivative retain only jet multiplicity).**

$$\forall m \in \mathbb{N}, rho \in \mathbb{C},\; \left(\forall s \in \mathbb{C},\; s \ne rho \Rightarrow \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, s\right)^{-1}\right) = \frac{m}{s - rho}\right) \land \left(\left(\forall s \in \mathbb{C},\; \operatorname{logDeriv}\left((z \mapsto \operatorname{det}\left(\operatorname{jetPencil}\left(m, rho, z\right)\right)), s\right) = \frac{m}{s - rho}\right) \land \left(\operatorname{MeromorphicAt}\left((z \mapsto \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), rho\right) \land \left(\left(0 < m \Rightarrow \operatorname{meromorphicOrderAt}\left((z \mapsto \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), rho\right) = -1\right) \land \operatorname{Tendsto}\left((z \mapsto {z - rho} \times \operatorname{trace}\left(\operatorname{jetPencil}\left(m, rho, z\right)^{-1}\right)), \operatorname{nhdsWithin}\left(rho, \mathbb{C} \setminus \{rho\}\right), \operatorname{nhds}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For length m, nilpotentJetShift has value one exactly one step below the diagonal and zero elsewhere. The named jetPencil is (s-rho) times the identity minus that shift.

Only the exact-order clause assumes positive length, so its jet weight is nonzero. The length-zero pencil instead has determinant one and trace resolvent zero, and therefore has no pole. Only the pointwise trace identity requires s != rho, its exact invertibility domain.

Lower triangularity makes the pencil determinant (s-rho)^m and every diagonal inverse entry (s-rho)^(-1). Summing the diagonal and differentiating the determinant give the two displayed identities. The punctured identity also proves that the trace resolvent is meromorphic with order minus one and that multiplication by s-rho converges to the residue m.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/JetResolventSemisimplification.jet_resolvent_semisimplification`
