# The original 252 modular rows

## Abstract

Literal input for the fixed 252-row core after removing moduli divisible by 23. Coefficients, moduli and integer phase domains are unchanged.

**Definition 1.1 (Original congruence row).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.Row`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row stores the prime label p, original modulus e, and original coefficients a,b as natural numbers.

**Definition 1.2 (Common original period).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.period`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.period` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The period is the literal natural number 17599117536000. It is the least common multiple of the 252 retained original moduli.

**Definition 1.3 (Seven base rows).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.baseRows`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.baseRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven original rows have prime labels 5,7,11,13,17,19,23 and moduli 4,6,10,12,16,18,11, with their original coefficients.

**Definition 1.4 (Remaining original rows).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.tailRows`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.tailRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 245 literal tail rows follow the seven base rows in the original input order. Precisely the input rows with modulus divisible by 23 are omitted.

**Definition 1.5 (One global phase vector).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.Phases`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.Phases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Phases is Fin 252 to integers. Its value at a row is fixed before either exponent coordinate is chosen.

**Definition 1.6 (Common translation of phases).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.shiftPhases`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.shiftPhases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At row i, shiftPhases c t subtracts a_i times t.1 plus b_i times t.2 from c i. The same t is used for every row.

**Definition 1.7 (Canonical phase domain sizes).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.phaseDomain`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.phaseDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven sizes are 1,1,2,2,4,6,1.

**Definition 1.8 (Canonical base phases).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.Canonical`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.Canonical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each of the first seven rows, the integer remainder of its assigned phase modulo its original modulus is less than its corresponding phaseDomain size.

**Definition 1.9 (Original rows).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.rows`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seven base rows followed by the remaining 245 original rows. The modulus-11 row labelled by prime 23 is retained.

**Definition 1.10 (Original congruence events).**

Lean statement: `D5/S3/Arith/Covering/Erdos203Rows.hits`

*Formalization.* `D5/S3/Arith/Covering/Erdos203Rows.hits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer linear form is compared with a fixed original phase modulo the row modulus.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.Canonical`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.Phases`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.Row`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.baseRows`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.hits`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.period`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.phaseDomain`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.rows`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.shiftPhases`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203Rows.tailRows`
