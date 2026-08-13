# Golden Desubstitution Normal Form

## Abstract

Organize golden desubstitution as a terminating deterministic rewrite system and identify its unique terminal indices.

**Definition 1.1 (One golden desubstitution step).**

$$\operatorname{desubStep}(x, y)\iff x\neq0 \land \operatorname{goldenSubstStart}(y)=x$$

*Formalization.* `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonzero substitution-block boundary rewrites to the unique source index whose block begins there.

**Theorem 1.2 (Each desubstitution step strictly decreases the index).**

$$\forall x,y\in\mathbb{N},\ \operatorname{desubStep}(x,y) \Rightarrow y<x$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive source prefix contains the initial true letter, so its substitution boundary lies strictly beyond the source index.

**Theorem 1.3 (Golden desubstitution terminates).**

$$\operatorname{WellFounded}(\operatorname{swap}(\operatorname{desubStep}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_termination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural index is a well-founded measure because every reverse-edge predecessor is strictly smaller.

**Theorem 1.4 (Golden desubstitution is deterministic).**

$$\forall x,y,z\in\mathbb{N},\ \operatorname{desubStep}(x,y) \land \operatorname{desubStep}(x,z) \Rightarrow y=z$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict monotonicity makes the block-start map injective, so one boundary cannot have two source indices.

**Theorem 1.5 (Golden desubstitution is locally confluent).**

$$\forall h,a,b,\ \operatorname{desubStep}(h,a) \land \operatorname{desubStep}(h,b) \Rightarrow \exists c, \operatorname{ReflTransGen}(\operatorname{desubStep})(a,c) \land \operatorname{ReflTransGen}(\operatorname{desubStep})(b,c)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_localConfluence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deterministic one-step reducts are equal, so both branches join reflexively at that common reduct.

**Theorem 1.6 (Terminal indices are zero or false golden-word positions).**

$$\neg\exists x, \operatorname{desubStep}(m,x) \iff m=0 \lor \operatorname{goldenWord}(m)=false$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_irreducible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recognizability identifies every true position with a substitution-block boundary. The nonzero guard leaves zero irreducible and prevents the boundary at zero from becoming a self-loop.

**Theorem 1.7 (Every index has a unique golden desubstitution terminal).**

$$\forall n\in\mathbb{N},\ \exists! m, \operatorname{ReflTransGen}(\operatorname{desubStep})(n,m) \land \left(m=0 \lor \operatorname{goldenWord}(m)=false\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.golden_desubstitution_unique_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen abstract Newman theorem applies to strict descent and the deterministic local-confluence join. Replacing irreducibility by its golden-word characterization gives the stated unique terminal.

## References

- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_deterministic`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_irreducible_iff`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_localConfluence`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_lt`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_termination`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.golden_desubstitution_unique_terminal`
- Dependency: [D5/S0/Rewriting/Newman](../../../S0/Rewriting/Newman.md)
