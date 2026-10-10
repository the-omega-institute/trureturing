# Prime Triplet Wheel Reflection

## Abstract

Reflection preserves the cardinality of the two oriented wheel candidate spaces at every nonzero modulus.

**Theorem 1.1 (The affine wheel reflection is an involution).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.reflect_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.reflect_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero modulus W, the map a ↦ -a-6 on ZMod W is its own inverse. This is the transport map between the two orientation charts.

**Theorem 1.2 (Reflection exchanges wheel admissibility).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.plus_reflect_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.plus_reflect_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A residue is admissible for {0,2,6} exactly when its reflected residue is admissible for {0,4,6}. The proof uses only that negation preserves units and that the three offsets are paired by the affine reflection.

**Definition 1.3 (The two candidate spaces are equivalent).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.reflectEquiv`

*Formalization.* `D5/S3/Arith/PrimeTripletWheel.reflectEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype of H-plus wheel candidates and the subtype of H-minus wheel candidates are equivalent finite spaces. This packages the orientation symmetry before any choice of origin or observation chart.

**Theorem 1.4 (Oriented candidate spaces have equal cardinality).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.candidate_space_card_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.candidate_space_card_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero modulus, the two oriented wheel candidate spaces have equal cardinality. The statement locally supplies Fintype.ofFinite instances for both residue subtypes; its only hypothesis is NeZero W. This is a general density-symmetry theorem for finite wheel candidates; it makes no claim about infinitude, asymptotics, or the actual distribution of prime triplets.

**Theorem 1.5 (The plus candidates modulo 30 are 11 and 17).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.plus_residues_30`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.plus_residues_30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite plus wheel candidate set in Fin 30 is exactly {11,17}; this is a kernel-checked finite arithmetic certificate.

**Theorem 1.6 (The minus candidates modulo 30 are 7 and 13).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.minus_residues_30`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.minus_residues_30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite minus wheel candidate set in Fin 30 is exactly {7,13}; this is a kernel-checked finite arithmetic certificate.

**Theorem 1.7 (The plus origin prefix through 10 is empty).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.plus_origin_prefix_30`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.plus_origin_prefix_30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among residues 1 through 10 modulo 30, no plus wheel candidate occurs.

**Theorem 1.8 (The minus origin prefix through 10 has one candidate).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.minus_origin_prefix_30`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.minus_origin_prefix_30` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among residues 1 through 10 modulo 30, exactly one minus wheel candidate occurs.

**Theorem 1.9 (The plus ordered triple readout at shifts 6 and 30 is one).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.plus_triple_readout_210`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.plus_triple_readout_210` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus 210, exactly one plus candidate remains a candidate after both shifts 6 and 30.

**Theorem 1.10 (The minus ordered triple readout at shifts 6 and 30 is zero).**

Lean statement: `D5/S3/Arith/PrimeTripletWheel.minus_triple_readout_210`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimeTripletWheel.minus_triple_readout_210` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At modulus 210, no minus candidate remains a candidate after both shifts 6 and 30.

## References

- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.candidate_space_card_eq`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.minus_origin_prefix_30`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.minus_residues_30`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.minus_triple_readout_210`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.plus_origin_prefix_30`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.plus_reflect_iff`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.plus_residues_30`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.plus_triple_readout_210`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.reflectEquiv`
- Truth anchor: `D5/S3/Arith/PrimeTripletWheel.reflect_involutive`
