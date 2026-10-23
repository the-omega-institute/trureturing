# ParentCoordinates

## Abstract

A world keeps the single matrix P(r,b), one fixed drift d and one whole nonzero real polynomial of degree at most three

A world keeps the single matrix P(r,b), one fixed drift d and one whole nonzero real polynomial of degree at most three. The chronological action list is [J,M,J,M,M,M], acting by left multiplication. The initial read counts and the first five literal readings are [0,24,147/5,24,18]. No reset, shifted clock or alternative jointly acquired reading is introduced.

Gain coordinates are the original values at clocks 0,1,2,3. The fixed-node Lagrange polynomial evaluates to these samples. Mathlib’s polynomial uniqueness theorem is applied directly to show that every polynomial of degree at most three has this representation; lower degrees, vanishing samples and repeated roots require no separate branch.

For ε=d-24, the parent equation is εΛ+(24/5)(b-1/8)(6/(1+b)-2/(1+2b))=0. Its gain samples are [-24-ε,-ε/j,(27/5-ε)/(1+b),-ε/n]. The literal fourth-row residual equals U times the parent equation. The equivalence reconstructs all five rows and the entire world, and its reverse direction uses only positive j,n,T,U as denominators.

The actual fifth and sixth M readings are P₅=24+(U+n)(96-108/T)+εA₅ and P₆=24+(2U+n)(240-243/T)+εA₆, where A₆=1+(2U+n)(10-36/j+45/T-20/n). These formulas come from the literal matrix products and the same gain. Unequal readings at clocks zero and one rule out only the identically zero gain.

**Theorem 1.1 (gainPoly eval).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every four-sample vector a and real clock s, evaluating gainPoly a at s gives exactly gain a s.

**Theorem 1.2 (gain samples).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.gain_samples`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.gain_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a : Fin 4 → ℝ and i : Fin 4, the gain evaluated at the original clock i equals aᵢ.

**Theorem 1.3 (gainPoly degree).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every four-sample vector a, gainPoly a has degree at most three; lower degrees and the zero polynomial satisfy the same estimate.

**Theorem 1.4 (polynomial representation).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.polynomial_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.polynomial_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real polynomial g of degree at most three equals gainPoly formed from g(0),g(1),g(2),g(3). Mathlib’s interpolation uniqueness identifies the reconstructed whole polynomial with g.

**Theorem 1.5 (literal traces).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.literal_traces`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.literal_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real r,b, the chronological traces at clocks zero through six are [1,j,1+b,n,1+2b,1+2b+n,2(1+2b)+n].

**Theorem 1.6 (source positivity).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.source_positivity`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.source_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0≤r≤1 and b>0, the quantities j,n,T=1+b and U=1+2b are all positive.

**Theorem 1.7 (actual m responses).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.actual_m_responses`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.actual_m_responses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate triple C, the literal readings of parentWorld C at clocks five and six equal fifthResponse C and sixthResponse C, using the same whole gain and fixed drift.

**Theorem 1.8 (parent gain nonzero).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.parent_gain_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.parent_gain_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every world satisfying the five literal parent rows has a nonzero whole gain polynomial. A zero polynomial would force the distinct readings at clocks zero and one to equal the same drift.

**Theorem 1.9 (fourth residual).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.fourth_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.fourth_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real r,b,d with j,n,T,U nonzero, the clock-four residual d+g(4)U-18 for the gain parentGain(r,b,d-24) equals U times parentEq(r,b,d-24).

**Theorem 1.10 (parent world iff).**

Lean statement: `D5/S3/Observer/CubicGain/ParentCoordinates.parent_world_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ParentCoordinates.parent_world_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every world W=(r,b,d,a) in sample coordinates, the conjunction of 0<r<1, b>0 and all five literal parent rows holds exactly when worldCoordinates W is a strict parent and parentWorld (worldCoordinates W) = W.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.actual_m_responses`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.fourth_residual`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_degree`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.gainPoly_eval`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.gain_samples`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.literal_traces`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.parent_gain_nonzero`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.parent_world_iff`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.polynomial_representation`
- Truth anchor: `D5/S3/Observer/CubicGain/ParentCoordinates.source_positivity`
- Dependency: [D5/S3/Observer/CubicGain/StrictDriftVector](StrictDriftVector.md)
