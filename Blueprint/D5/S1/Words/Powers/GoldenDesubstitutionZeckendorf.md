# Golden Desubstitution in Zeckendorf Coordinates

## Abstract

Identify golden substitution boundaries and terminal desubstitution indices through uniform shifts of canonical Zeckendorf digits.

**Theorem 1.1 (Golden substitution starts are displacement decodes).**

$$\forall n\in \mathbb{N},\ \operatorname{goldenSubstStart}(n)=\operatorname{displacementDecode}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_eq_displacement_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block-start count and the Zeckendorf displacement decode have the same shifted golden Beatty floor formula.

**Theorem 1.2 (A block start shifts every Zeckendorf digit once).**

$$\forall n\in \mathbb{N},\ \operatorname{wdigits}(\operatorname{goldenSubstStart}(n))=\operatorname{map}(k \mapsto k+1, \operatorname{wdigits}(n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_wdigits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniformly adding one preserves the nonadjacent Zeckendorf conditions, and uniqueness identifies the shifted list as the block start digits.

**Theorem 1.3 (Desubstitution paths are uniform digit shifts).**

$$\forall n,m\in \mathbb{N},\ \operatorname{ReflTransGen}(\operatorname{desubStep})(n,m) \iff \exists r, \operatorname{wdigits}(n)=\operatorname{map}(k \mapsto k+r, \operatorname{wdigits}(m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_path_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over the reflexive-transitive closure accumulates one digit shift per step; conversely, an explicit block-start iterate realizes every uniform shift.

**Theorem 1.4 (Terminal desubstitution is arithmetic in Zeckendorf digits).**

$$\forall n,m\in \mathbb{N},\ \left(\operatorname{ReflTransGen}(\operatorname{desubStep})(n,m) \land \left(m=0 \lor \operatorname{goldenWord}(m)=false\right)\right) \iff \left(\left(n=0 \land m=0\right) \lor \exists r, \left(2\in \operatorname{wdigits}(m) \land \operatorname{wdigits}(n)=\operatorname{map}(k \mapsto k+r, \operatorname{wdigits}(m))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_terminal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero path is isolated because zero has no occupied digits. Every other terminal has least digit two, exactly the false-letter criterion, while its ancestors are the uniform upward shifts of that digit list.

## References

- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_path_iff`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_terminal_iff`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_eq_displacement_decode`
- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_wdigits`
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](../../Deficit/ZeckendorfDisplacementReading.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionNormalForm](GoldenDesubstitutionNormalForm.md)
