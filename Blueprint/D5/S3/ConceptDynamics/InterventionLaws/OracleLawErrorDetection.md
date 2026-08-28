# Oracle Intervention-Law Error Detection

## Abstract

Exact intervention-law codewords decode uniquely below half their minimum coordinate distance.

**Theorem 1.1 (Oracle intervention-law errors have a unique decoding).**

$$\begin{aligned}\forall Model, Law: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Law\right)],\\n, e \in \mathbb{N},\\law: \operatorname{Fin}\left(n\right) \to \left(Model \to Law\right),\\M: Model, r: \operatorname{Fin}\left(n\right) \to Law,\\\operatorname{hammingDist}\left(r, \operatorname{jointReadout}\left(law, M\right)\right) \leq e \land 2 \times e < \operatorname{interventionMinimumDistance}\left(law\right) \Rightarrow\\\exists ! c: \operatorname{Fin}\left(n\right) \to Law,\\c \in \operatorname{range}\left(\operatorname{jointReadout}\left(law\right)\right) \land \operatorname{hammingDist}\left(r, c\right) \leq e.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionLaws/OracleLawErrorDetection.oracle_intervention_law_error_detection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite law suite sends each model to its canonical jointReadout codeword. Its minimum distance is constructed as the least Hamming distance between codewords arising from distinct models.

If the received law word differs from the true model codeword in at most e coordinates, any competing codeword in the same radius lies within 2e coordinates of it. The strict minimum-distance condition forces the competing codeword to equal the true one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionLaws/OracleLawErrorDetection.oracle_intervention_law_error_detection`
- Dependency: [D5/S3/Arith/Coding/UniqueDecodingRadius](../../Arith/Coding/UniqueDecodingRadius.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
