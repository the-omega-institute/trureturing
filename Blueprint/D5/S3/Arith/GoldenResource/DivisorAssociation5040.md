# 5040 Association Cardinality Anchors

## Abstract

The 5040 divisor count and the four-block association quotient are joined by explicit finite cardinality anchors.

The general association theorem counts sources and observed positions for every finite exponent box. This document records the exact specialization for the four-prime 5040 box and connects its sixty source coordinates to the existing positive-divisor count.

**Theorem 1.1 (Finite source-box cardinality).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The box (A,B,C,D) has (A+1)(B+1)(C+1)(D+1) sources.

**Theorem 1.2 (The 5040 source count).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The (4,2,1,1) exponent box has exactly 60 sources.

**Theorem 1.3 (The 5040 observed-position count).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.image_card_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociation5040.image_card_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The association image of the (4,2,1,1) box has exactly 48 positions, by the general image-card formula.

**Theorem 1.4 (Divisor/source count interface).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.divisor_5040_card_eq_box_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociation5040.divisor_5040_card_eq_box_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing GoldenDivisorLanguage theorem Nat.card (Div 5040)=60 is identified with the cardinality of the association source box. This is a finite count interface only; it does not identify the q coordinates with all divisor data and does not assert Robin's inequality or RH.

These anchors are intended as exact consumers for later source lifts. The 48-position quotient and the 60-source divisor count remain finite checks inside the already-proved general formula.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.box_card_5040`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.divisor_5040_card_eq_box_card`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociation5040.image_card_5040`
- Dependency: [D5/S3/Arith/GoldenResource/DivisorAssociationFiber](DivisorAssociationFiber.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenDivisorLanguage](GoldenDivisorLanguage.md)
