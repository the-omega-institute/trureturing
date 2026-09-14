# Shifted Width-Ten Schur Template

## Abstract

A finite compatibility check controls a shifted width-ten construction for Schur colorings.

**Definition 1.1 (Schur coloring).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.SchurColoring`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.SchurColoring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coloring of the positive integers through a bound is Schur when no equation x plus y equals z is monochromatic.

**Definition 1.2 (Existence of a Schur coloring).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.HasSchurColoring`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.HasSchurColoring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existence predicate records a coloring into a specified finite color set.

**Theorem 1.3 (Small values).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.schur_coloring_small_values`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schur_coloring_small_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One color suffices through one, two colors suffice through four, and one color cannot cover the interval through two.

**Theorem 1.4 (Classical threefold lift).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.schur_triple_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schur_triple_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two translated copies of an old coloring surround a middle interval assigned one fresh color.

**Definition 1.5 (Shifted template labels).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.ShiftedTemplateLabel`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.ShiftedTemplateLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two labels denote fresh colors, while two labels read the current or preceding color of the base coloring.

**Definition 1.6 (Width-ten row data).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplate`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row table assigns a label to each of ten columns, distinguishing the first row from every later row.

**Definition 1.7 (Finite compatibility conditions).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplateCompatible`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplateCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first row uses only legal shifts, every realizable main-row transition is sum-free, and every transition into the two terminal cells is sum-free.

**Definition 1.8 (Compatibility check).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three finite Boolean passes inspect legal first-row shifts, main-block transitions, and terminal transitions.

**Theorem 1.9 (Soundness of the check).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful Boolean check supplies every compatibility condition used by the coloring construction.

**Definition 1.10 (The recorded width-ten rows).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.tableIITemplate`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.tableIITemplate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Table II of arXiv:2607.15034 records the first row B, A, P0, P0, B, A, A, B, P0, P0 and the later row P-1, B, P0, P0, B, A, A, B, P0, P0.

**Definition 1.11 (The recorded terminal pair).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.tableIITail`

*Formalization.* `D5/S3/Arith/SchurShiftedTemplateLift.tableIITail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same table records the two terminal labels A and B.

**Theorem 1.12 (Finite compatibility and block arithmetic).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.tableII_finite_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.tableII_finite_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recorded rows and terminal pair pass the finite check. For positive summands, division into width-ten rows and columns expresses addition by one row carry and the corresponding column residue.

**Theorem 1.13 (Shifted width-ten lift).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.schur_shifted_widthTen_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schur_shifted_widthTen_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Schur coloring through n extends to a coloring through ten n plus two after two fresh colors are added.

**Theorem 1.14 (Numerical consequences).**

Lean statement: `D5/S3/Arith/SchurShiftedTemplateLift.schur_numerical_fidelity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schur_numerical_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classical lift gives a three-coloring through thirteen, and the shifted lift gives a four-coloring through forty-two.

## References

- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.HasSchurColoring`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.SchurColoring`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.ShiftedTemplateLabel`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplate`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.WidthTenTemplateCompatible`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.checkWidthTenTemplate_sound`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schur_coloring_small_values`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schur_numerical_fidelity`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schur_shifted_widthTen_lift`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schur_triple_lift`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.tableIITail`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.tableIITemplate`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.tableII_finite_compatibility`
