# Explicit extended Golay code

## Abstract

Explicit extended Golay code

**Definition 1.1 (Carryless polynomial encoding).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode`

*Formalization.* `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode` (`✓ std3`).

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The actual linear map from twelve binary message coordinates to twenty-four coordinates multiplies by g, with no wraparound, and appends its parity coordinate.

**Theorem 1.2 (The reciprocal convention is identified exactly).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.reference_encoder_identification`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.reference_encoder_identification` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The reference polynomial from Elkies is related by explicit reversal of the message and first twenty-three coordinate positions, fixing parity.

**Theorem 1.3 (The last coordinate is the parity bit).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.parity_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.parity_extension` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The twenty-fourth coordinate equals the binary sum of the first twenty-three coordinates for every message.

**Theorem 1.4 (The encoder loses no messages).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode_injective` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

A finite matrix inverse certificate proves a left inverse, hence injectivity of the actual encoder.

**Theorem 1.5 (Dimension twelve).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_finrank` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The linear image has dimension twelve by injectivity and upstream linear algebra.

**Theorem 1.6 (All 4096 messages remain distinct).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_card` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The actual linear image has exactly 4096 words.

**Theorem 1.7 (Kernel-checked weights of all actual words).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.weight_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.weight_spectrum` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

Sixty-four small kernel certificates cover all 4096 messages. The only weights are zero, eight, twelve, sixteen and twenty-four. This is a spectrum assertion, not an exact enumerator count.

**Theorem 1.8 (Double evenness).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.doubly_even`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.doubly_even` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

Every word in the actual linear image has Hamming weight divisible by four.

**Theorem 1.9 (Nonzero words have weight at least eight).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.minimum_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.minimum_weight` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The computed spectrum together with the weight-zero characterization yields the universal lower bound.

**Theorem 1.10 (The all-ones carry word belongs).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.all_ones_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.all_ones_mem` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The encoder applied to message 3189 is the actual all-ones word needed for odd plus odd integer-vector closure.

**Theorem 1.11 (The encoded octad belongs to the linear image).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_mem` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

Its message witness is retained by the actual encoder-image definition and is consumed by the shortest-vector construction.

**Theorem 1.12 (An encoded weight-eight word).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_weight` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The octad is the encoder applied to message one, not a separately supplied codeword.

**Theorem 1.13 (Orthogonality from the generator).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_orthogonal` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The actual generator has zero Gram matrix, yielding orthogonality of every pair of its linear-image words.

**Theorem 1.14 (Self-duality).**

Lean statement: `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_dual` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

A small kernel-checked matrix splitting identity reconstructs every orthogonal vector through the actual encoder, giving equality with the orthogonal complement.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.all_ones_mem`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_card`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.code_finrank`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.doubly_even`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.encode_injective`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.minimum_weight`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_mem`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.octad_weight`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.parity_extension`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.reference_encoder_identification`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_dual`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.self_orthogonal`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/GolayEncoder.weight_spectrum`
