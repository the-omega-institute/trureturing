# The complete dense broken-Heawood deletion certificate

## Abstract

The complete dense broken-Heawood deletion certificate

The original Boolean star reflection is proved, then all sixty-four chunks of two hundred fifty-six masks cover all 16384 subsets of the fixed fourteen-vertex block. Every selection of size at least nine has a safely deletable nonport vertex. The result is consumed by the arbitrary ambient cap, rather than treating a finite graph check as an all-size family proof.

**Definition 1.1 (brokenNeighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.brokenNeighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.brokenNeighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def brokenNeighbors (vertex : Fin 14) : List (Fin 14).

**Definition 1.2 (BrokenAdj).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.BrokenAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.BrokenAdj` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def BrokenAdj (first second : Fin 14) : Prop.

**Theorem 1.3 (broken simple).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.broken_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.broken_simple` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem broken_simple : (∀ vertex : Fin 14, ¬ BrokenAdj vertex vertex) ∧ (∀ first second : Fin 14, BrokenAdj first second ↔ BrokenAdj second first).

**Definition 1.4 (chosen).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.chosen`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.chosen` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def chosen (mask : Nat) (vertex : Fin 14) : Bool.

**Definition 1.5 (kept).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.kept`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.kept` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def kept (mask : Nat) (deleted vertex : Fin 14) : Bool.

**Definition 1.6 (selectedCard).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.selectedCard`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.selectedCard` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selectedCard (mask : Nat) : Nat.

**Definition 1.7 (starBool).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def starBool (selection : Fin 14 → Bool) (outside : Fin 14) : Bool.

**Theorem 1.8 (starBool correct).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool_correct` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem starBool_correct (selection : Fin 14 → Bool) (outside : Fin 14) : starBool selection outside = true ↔ TwoAt BrokenAdj (fun vertex => selection vertex = true) outside.

**Definition 1.9 (safeBool).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def safeBool (mask : Nat) (deleted : Fin 14) : Bool.

**Definition 1.10 (Safe).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.Safe`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.Safe` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Safe (mask : Nat) (deleted : Fin 14) : Prop.

**Theorem 1.11 (safeBool correct).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool_correct` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem safeBool_correct (mask : Nat) (deleted : Fin 14) (hsafe : safeBool mask deleted = true) : Safe mask deleted.

**Definition 1.12 (denseChunk).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.denseChunk`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CubicDense.denseChunk` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def denseChunk (chunk : Nat) : Bool.

**Theorem 1.13 (dense chunk 0).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_0` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_0 : denseChunk 0 = true.

**Theorem 1.14 (dense chunk 1).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_1`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_1` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_1 : denseChunk 1 = true.

**Theorem 1.15 (dense chunk 2).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_2`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_2` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_2 : denseChunk 2 = true.

**Theorem 1.16 (dense chunk 3).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_3`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_3` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_3 : denseChunk 3 = true.

**Theorem 1.17 (dense chunk 4).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_4`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_4` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_4 : denseChunk 4 = true.

**Theorem 1.18 (dense chunk 5).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_5`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_5` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_5 : denseChunk 5 = true.

**Theorem 1.19 (dense chunk 6).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_6`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_6` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_6 : denseChunk 6 = true.

**Theorem 1.20 (dense chunk 7).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_7`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_7` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_7 : denseChunk 7 = true.

**Theorem 1.21 (dense chunk 8).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_8`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_8` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_8 : denseChunk 8 = true.

**Theorem 1.22 (dense chunk 9).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_9`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_9` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_9 : denseChunk 9 = true.

**Theorem 1.23 (dense chunk 10).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_10`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_10` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_10 : denseChunk 10 = true.

**Theorem 1.24 (dense chunk 11).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_11`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_11` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_11 : denseChunk 11 = true.

**Theorem 1.25 (dense chunk 12).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_12`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_12` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_12 : denseChunk 12 = true.

**Theorem 1.26 (dense chunk 13).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_13`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_13` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_13 : denseChunk 13 = true.

**Theorem 1.27 (dense chunk 14).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_14`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_14` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_14 : denseChunk 14 = true.

**Theorem 1.28 (dense chunk 15).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_15`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_15` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_15 : denseChunk 15 = true.

**Theorem 1.29 (dense chunk 16).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_16`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_16` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_16 : denseChunk 16 = true.

**Theorem 1.30 (dense chunk 17).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_17`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_17` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_17 : denseChunk 17 = true.

**Theorem 1.31 (dense chunk 18).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_18`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_18` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_18 : denseChunk 18 = true.

**Theorem 1.32 (dense chunk 19).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_19`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_19` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_19 : denseChunk 19 = true.

**Theorem 1.33 (dense chunk 20).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_20`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_20` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_20 : denseChunk 20 = true.

**Theorem 1.34 (dense chunk 21).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_21`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_21` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_21 : denseChunk 21 = true.

**Theorem 1.35 (dense chunk 22).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_22`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_22` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_22 : denseChunk 22 = true.

**Theorem 1.36 (dense chunk 23).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_23`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_23` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_23 : denseChunk 23 = true.

**Theorem 1.37 (dense chunk 24).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_24`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_24` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_24 : denseChunk 24 = true.

**Theorem 1.38 (dense chunk 25).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_25`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_25` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_25 : denseChunk 25 = true.

**Theorem 1.39 (dense chunk 26).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_26`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_26` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_26 : denseChunk 26 = true.

**Theorem 1.40 (dense chunk 27).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_27`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_27` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_27 : denseChunk 27 = true.

**Theorem 1.41 (dense chunk 28).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_28`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_28` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_28 : denseChunk 28 = true.

**Theorem 1.42 (dense chunk 29).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_29`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_29` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_29 : denseChunk 29 = true.

**Theorem 1.43 (dense chunk 30).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_30`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_30` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_30 : denseChunk 30 = true.

**Theorem 1.44 (dense chunk 31).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_31`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_31` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_31 : denseChunk 31 = true.

**Theorem 1.45 (dense chunk 32).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_32`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_32` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_32 : denseChunk 32 = true.

**Theorem 1.46 (dense chunk 33).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_33`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_33` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_33 : denseChunk 33 = true.

**Theorem 1.47 (dense chunk 34).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_34`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_34` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_34 : denseChunk 34 = true.

**Theorem 1.48 (dense chunk 35).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_35`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_35` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_35 : denseChunk 35 = true.

**Theorem 1.49 (dense chunk 36).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_36`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_36` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_36 : denseChunk 36 = true.

**Theorem 1.50 (dense chunk 37).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_37`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_37` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_37 : denseChunk 37 = true.

**Theorem 1.51 (dense chunk 38).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_38`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_38` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_38 : denseChunk 38 = true.

**Theorem 1.52 (dense chunk 39).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_39`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_39` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_39 : denseChunk 39 = true.

**Theorem 1.53 (dense chunk 40).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_40`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_40` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_40 : denseChunk 40 = true.

**Theorem 1.54 (dense chunk 41).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_41`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_41` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_41 : denseChunk 41 = true.

**Theorem 1.55 (dense chunk 42).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_42`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_42` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_42 : denseChunk 42 = true.

**Theorem 1.56 (dense chunk 43).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_43`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_43` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_43 : denseChunk 43 = true.

**Theorem 1.57 (dense chunk 44).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_44`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_44` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_44 : denseChunk 44 = true.

**Theorem 1.58 (dense chunk 45).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_45`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_45` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_45 : denseChunk 45 = true.

**Theorem 1.59 (dense chunk 46).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_46`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_46` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_46 : denseChunk 46 = true.

**Theorem 1.60 (dense chunk 47).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_47`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_47` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_47 : denseChunk 47 = true.

**Theorem 1.61 (dense chunk 48).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_48`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_48` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_48 : denseChunk 48 = true.

**Theorem 1.62 (dense chunk 49).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_49`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_49` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_49 : denseChunk 49 = true.

**Theorem 1.63 (dense chunk 50).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_50`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_50` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_50 : denseChunk 50 = true.

**Theorem 1.64 (dense chunk 51).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_51`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_51` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_51 : denseChunk 51 = true.

**Theorem 1.65 (dense chunk 52).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_52`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_52` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_52 : denseChunk 52 = true.

**Theorem 1.66 (dense chunk 53).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_53`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_53` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_53 : denseChunk 53 = true.

**Theorem 1.67 (dense chunk 54).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_54`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_54` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_54 : denseChunk 54 = true.

**Theorem 1.68 (dense chunk 55).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_55`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_55` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_55 : denseChunk 55 = true.

**Theorem 1.69 (dense chunk 56).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_56`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_56` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_56 : denseChunk 56 = true.

**Theorem 1.70 (dense chunk 57).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_57`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_57` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_57 : denseChunk 57 = true.

**Theorem 1.71 (dense chunk 58).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_58`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_58` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_58 : denseChunk 58 = true.

**Theorem 1.72 (dense chunk 59).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_59`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_59` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_59 : denseChunk 59 = true.

**Theorem 1.73 (dense chunk 60).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_60`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_60` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_60 : denseChunk 60 = true.

**Theorem 1.74 (dense chunk 61).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_61`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_61` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_61 : denseChunk 61 = true.

**Theorem 1.75 (dense chunk 62).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_62`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_62` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_62 : denseChunk 62 = true.

**Theorem 1.76 (dense chunk 63).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_63`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_63` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_chunk_63 : denseChunk 63 = true.

**Theorem 1.77 (all dense chunks).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.all_dense_chunks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.all_dense_chunks` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem all_dense_chunks : ∀ chunk : Fin 64, denseChunk chunk.val = true | ⟨0, _⟩ => dense_chunk_0 | ⟨1, _⟩ => dense_chunk_1 | ⟨2, _⟩ => dense_chunk_2 | ⟨3, _⟩ => dense_chunk_3 | ⟨4, _⟩ => dense_chunk_4 | ⟨5, _⟩ => dense_chunk_5 | ⟨6, _⟩ => dense_chunk_6 | ⟨7, _⟩ => dense_chunk_7 | ⟨8, _⟩ => dense_chunk_8 | ⟨9, _⟩ => dense_chunk_9 | ⟨10, _⟩ => dense_chunk_10 | ⟨11, _⟩ => dense_chunk_11 | ⟨12, _⟩ => dense_chunk_12 | ⟨13, _⟩ => dense_chunk_13 | ⟨14, _⟩ => dense_chunk_14 | ⟨15, _⟩ => dense_chunk_15 | ⟨16, _⟩ => dense_chunk_16 | ⟨17, _⟩ => dense_chunk_17 | ⟨18, _⟩ => dense_chunk_18 | ⟨19, _⟩ => dense_chunk_19 | ⟨20, _⟩ => dense_chunk_20 | ⟨21, _⟩ => dense_chunk_21 | ⟨22, _⟩ => dense_chunk_22 | ⟨23, _⟩ => dense_chunk_23 | ⟨24, _⟩ => dense_chunk_24 | ⟨25, _⟩ => dense_chunk_25 | ⟨26, _⟩ => dense_chunk_26 | ⟨27, _⟩ => dense_chunk_27 | ⟨28, _⟩ => dense_chunk_28 | ⟨29, _⟩ => dense_chunk_29 | ⟨30, _⟩ => dense_chunk_30 | ⟨31, _⟩ => dense_chunk_31 | ⟨32, _⟩ => dense_chunk_32 | ⟨33, _⟩ => dense_chunk_33 | ⟨34, _⟩ => dense_chunk_34 | ⟨35, _⟩ => dense_chunk_35 | ⟨36, _⟩ => dense_chunk_36 | ⟨37, _⟩ => dense_chunk_37 | ⟨38, _⟩ => dense_chunk_38 | ⟨39, _⟩ => dense_chunk_39 | ⟨40, _⟩ => dense_chunk_40 | ⟨41, _⟩ => dense_chunk_41 | ⟨42, _⟩ => dense_chunk_42 | ⟨43, _⟩ => dense_chunk_43 | ⟨44, _⟩ => dense_chunk_44 | ⟨45, _⟩ => dense_chunk_45 | ⟨46, _⟩ => dense_chunk_46 | ⟨47, _⟩ => dense_chunk_47 | ⟨48, _⟩ => dense_chunk_48 | ⟨49, _⟩ => dense_chunk_49 | ⟨50, _⟩ => dense_chunk_50 | ⟨51, _⟩ => dense_chunk_51 | ⟨52, _⟩ => dense_chunk_52 | ⟨53, _⟩ => dense_chunk_53 | ⟨54, _⟩ => dense_chunk_54 | ⟨55, _⟩ => dense_chunk_55 | ⟨56, _⟩ => dense_chunk_56 | ⟨57, _⟩ => dense_chunk_57 | ⟨58, _⟩ => dense_chunk_58 | ⟨59, _⟩ => dense_chunk_59 | ⟨60, _⟩ => dense_chunk_60 | ⟨61, _⟩ => dense_chunk_61 | ⟨62, _⟩ => dense_chunk_62 | ⟨63, _⟩ => dense_chunk_63 | ⟨remaining + 64, hbound⟩ => by omega theorem dense_certificate (mask : Fin 16384) (hcard : 9 ≤ selectedCard mask.val) : ∃ deleted, Safe mask.val deleted.

**Theorem 1.78 (dense certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem dense_certificate (mask : Fin 16384) (hcard : 9 ≤ selectedCard mask.val) : ∃ deleted, Safe mask.val deleted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.BrokenAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.Safe`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.all_dense_chunks`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.brokenNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.broken_simple`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.chosen`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.denseChunk`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_1`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_10`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_11`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_12`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_13`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_14`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_15`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_16`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_17`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_18`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_19`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_20`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_21`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_22`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_23`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_24`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_25`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_26`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_27`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_28`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_29`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_3`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_30`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_31`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_32`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_33`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_34`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_35`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_36`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_37`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_38`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_39`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_4`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_40`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_41`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_42`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_43`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_44`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_45`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_46`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_47`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_48`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_49`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_5`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_50`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_51`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_52`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_53`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_54`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_55`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_56`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_57`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_58`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_59`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_6`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_60`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_61`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_62`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_63`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_7`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_8`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.dense_chunk_9`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.kept`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.safeBool_correct`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.selectedCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicDense.starBool_correct`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicCertificate](CubicCertificate.md)
