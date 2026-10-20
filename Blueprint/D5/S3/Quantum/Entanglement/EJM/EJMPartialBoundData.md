# Every actual row field remains available to the checker

## Abstract

Untrusted original local partial-bound data with an explicit total decoder.

The local orbit DAGs contain 41294 triangle rows in ten-coordinate order and 8689 singleton rows in nine-coordinate order. RawRow records either a terminal hash and integer bound or a branch hash, bound, split coordinate, packed children and packed actions. RawTree stores packed natural-number payloads. Each row occupies 164 bits: a 24-bit base-five hash, 32-bit biased signed bound, 8-bit coordinate, four 16-bit children and four 9-bit actions; 128 rows occupy each stored natural number. These definitions supply proposed rows, not mathematical validity. The complete actual structural checks, exact local actions, terminal inequalities and contraction values must be earned by their kernel consumers before any local acceptance theorem follows.

**Definition 1.1 (Packed natural-number dictionary lookup).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.get`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.get` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary interpreter returns a matching payload, follows the query ordering to a child, and returns zero on an empty lookup. No producer assertion participates in this interpretation.

**Definition 1.2 (Decode the original 164-bit row fields).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.unpack`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.unpack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder reads the fixed bit fields, subtracts 2147483648 from the signed-bound field, and uses coordinate equal to the supplied dimension as the terminal tag. Other coordinates give a branch retaining all four children and actions.

**Definition 1.3 (Select one original row from a packed payload).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.read`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.read` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row index selects a stored natural via division by 128 and selects its 164-bit field via the remainder. This total decoding function is data access and does not prove its decoded row passes a check.

**Definition 1.4 (The exact recorded-bound scale).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.scale`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer scale is 6987435. The actual row interpreter multiplies each recorded lower bound by this same scale; all later inequalities concern the resulting integer value.

**Definition 1.5 (Base-five coordinate decoding).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.digit`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A hash coordinate is its base-five digit, using natural-number division and remainder. Outcomes zero through three are known values and digit four represents unknown in a partial event.

**Definition 1.6 (Decode the actual partial assignment).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.partialEvent`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.partialEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Digits below four produce the corresponding known Fin 4 outcome. Other digits produce none, preserving the original partial-assignment semantics used by every compatibility and transport check.

**Definition 1.7 (Decode a total four-valued event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.event`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.event` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each base-five digit is reduced modulo four to produce a total Fin 4 outcome. Whether a decoded complete event matches its stored partial assignment is a separate checker obligation.

**Definition 1.8 (Twenty-four literal common-outcome maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.outcome`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.outcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table defines the actual common outcome functions used by local actions. Their bijectivity and compatibility/score transport laws are proved in the separate local transport consumer; the table alone supplies no such theorem.

**Definition 1.9 (Decode a local coordinate/outcome action tag).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.action`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code gives a Fin 12 coordinate index and Fin 24 outcome index using division by 24 and the indicated modular reductions. LocalSym is the corresponding pair type.

**Definition 1.10 (Interpret every original raw row as a complete or split rule).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.row`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interpreter scales the bound, decodes the partial event, and constructs the actual complete event or all four split children/actions. Coordinate and child indices are reduced into their finite domains. These totality conversions do not replace checks of exact assignments, earlier-child order, lower-bound direction or terminal score inequalities.

**Definition 1.11 (The complete packed triangle data tree).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleTree`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This tree assembles the original packed payloads for all triangle rows. It is a concrete input to the decoder, without an assumed checkStructure or checkRow acceptance theorem.

**Definition 1.12 (The actual 41294 triangle rows).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleRows`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each row is read from the complete triangle tree and interpreted with dimension ten and the actual row count. Every structural and numerical consumer uses this same row function.

**Definition 1.13 (The complete packed singleton data tree).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonTree`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the corresponding original singleton payload tree. Storing a claimed lower bound does not prove that bound at a terminal event or every compatible completion.

**Definition 1.14 (The actual 8689 singleton rows).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonRows`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singleton row function uses the original tree, dimension nine and actual row count. Full row acceptance requires all actual premises to be kernel-checked in the downstream certificate.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.action`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.digit`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.event`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.get`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.outcome`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.partialEvent`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.read`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.row`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.scale`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonRows`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.singletonTree`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleRows`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.triangleTree`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundData.unpack`
- Dependency: [D5/S0/Certificates/FinitePartialBoundDAG](../../../../S0/Certificates/FinitePartialBoundDAG.md)
