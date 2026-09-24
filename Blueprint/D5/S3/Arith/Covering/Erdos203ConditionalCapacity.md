# A uniform positive hole bound for the original 252 rows

## Abstract

For every original 252-phase vector, the uncovered fraction on period M=17599117536000 is at least 41512904387/2792167686000. No single globally fixed phase vector covers all integer exponent points. These conclusions concern the specified 252 rows only.

**Definition 1.1 (Uncovered points at the original phases).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.Holes`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.Holes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Holes c is the set of points in (ZMod M) squared missed by every one of the 252 original linear congruences at the unchanged phase vector c.

**Definition 1.2 (Existence of a globally fixed covering phase vector).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.globalCover`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.globalCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asks whether there exists one original phase vector c such that for every pair of integers x,y, some original row hits its assigned phase c i. The existential phase vector is chosen before both exponent coordinates. This is the construction possibility for the supplied rows, not a published conjecture or the whole Erdos 203 assertion.

**Theorem 1.3 (The exact uniform positive gap).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.uniform_hole_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.uniform_hole_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unchanged original phase vector c, 41512904387 times M squared is at most 2792167686000 times the cardinality of Holes c. Equivalently, every c has at least 4604933957031786373632000 holes. The canonical conditional union estimate uses all 96 certificates defined in this module; one common translation gives a bijection of hole sets and returns the bound to the original phases. The certificate equations and digit bounds give the required arithmetic inequalities. The bound does not assert simultaneous attainment of the separate histogram maxima or the minimum actual hole count.

**Theorem 1.4 (No global covering phase vector).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed theorem has type Not globalCover. Given a proposed covering phase vector, it normalizes that vector, uses the certified canonical conditional union estimate to construct a missed torus point, lifts both coordinates to integers, and translates them back together. The original-row event equivalence contradicts coverage at that integer pair. The 285-row composition and the whole Erdos 203 problem remain outside the conclusion.

**Definition 1.5 (Arithmetic certificate for class 0).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate0`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.6 (Arithmetic certificate for class 1).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate1`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.7 (Arithmetic certificate for class 2).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate2`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.8 (Arithmetic certificate for class 3).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate3`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.9 (Arithmetic certificate for class 4).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate4`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.10 (Arithmetic certificate for class 5).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate5`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.11 (Arithmetic certificate for class 6).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate6`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.12 (Arithmetic certificate for class 7).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate7`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.13 (Arithmetic certificate for class 8).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate8`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.14 (Arithmetic certificate for class 9).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate9`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.15 (Arithmetic certificate for class 10).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate10`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.16 (Arithmetic certificate for class 11).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate11`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.17 (Arithmetic certificate for class 12).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate12`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.18 (Arithmetic certificate for class 13).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate13`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.19 (Arithmetic certificate for class 14).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate14`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.20 (Arithmetic certificate for class 15).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate15`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.21 (Arithmetic certificate for class 16).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate16`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.22 (Arithmetic certificate for class 17).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate17`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate17` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.23 (Arithmetic certificate for class 18).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate18`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate18` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.24 (Arithmetic certificate for class 19).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate19`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.25 (Arithmetic certificate for class 20).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate20`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.26 (Arithmetic certificate for class 21).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate21`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.27 (Arithmetic certificate for class 22).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate22`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate22` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.28 (Arithmetic certificate for class 23).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate23`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate23` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.29 (Arithmetic certificate for class 24).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate24`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate24` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.30 (Arithmetic certificate for class 25).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate25`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate25` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.31 (Arithmetic certificate for class 26).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate26`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate26` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.32 (Arithmetic certificate for class 27).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate27`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate27` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.33 (Arithmetic certificate for class 28).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate28`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate28` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.34 (Arithmetic certificate for class 29).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate29`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate29` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.35 (Arithmetic certificate for class 30).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate30`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate30` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.36 (Arithmetic certificate for class 31).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate31`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate31` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.37 (Arithmetic certificate for class 32).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate32`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate32` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.38 (Arithmetic certificate for class 33).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate33`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate33` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.39 (Arithmetic certificate for class 34).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate34`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate34` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.40 (Arithmetic certificate for class 35).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate35`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate35` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.41 (Arithmetic certificate for class 36).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate36`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate36` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.42 (Arithmetic certificate for class 37).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate37`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate37` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.43 (Arithmetic certificate for class 38).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate38`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate38` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.44 (Arithmetic certificate for class 39).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate39`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate39` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.45 (Arithmetic certificate for class 40).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate40`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate40` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.46 (Arithmetic certificate for class 41).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate41`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate41` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.47 (Arithmetic certificate for class 42).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate42`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate42` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.48 (Arithmetic certificate for class 43).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate43`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate43` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.49 (Arithmetic certificate for class 44).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate44`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate44` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.50 (Arithmetic certificate for class 45).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate45`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate45` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.51 (Arithmetic certificate for class 46).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate46`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate46` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.52 (Arithmetic certificate for class 47).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate47`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate47` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.53 (Arithmetic certificate for class 48).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate48`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate48` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.54 (Arithmetic certificate for class 49).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate49`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate49` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.55 (Arithmetic certificate for class 50).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate50`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate50` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.56 (Arithmetic certificate for class 51).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate51`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate51` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.57 (Arithmetic certificate for class 52).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate52`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate52` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.58 (Arithmetic certificate for class 53).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate53`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate53` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.59 (Arithmetic certificate for class 54).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate54`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate54` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.60 (Arithmetic certificate for class 55).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate55`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate55` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.61 (Arithmetic certificate for class 56).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate56`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate56` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.62 (Arithmetic certificate for class 57).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate57`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate57` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.63 (Arithmetic certificate for class 58).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate58`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate58` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.64 (Arithmetic certificate for class 59).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate59`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate59` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.65 (Arithmetic certificate for class 60).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate60`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate60` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.66 (Arithmetic certificate for class 61).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate61`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate61` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.67 (Arithmetic certificate for class 62).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate62`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate62` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.68 (Arithmetic certificate for class 63).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate63`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate63` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.69 (Arithmetic certificate for class 64).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate64`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate64` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.70 (Arithmetic certificate for class 65).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate65`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate65` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.71 (Arithmetic certificate for class 66).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate66`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate66` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.72 (Arithmetic certificate for class 67).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate67`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate67` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.73 (Arithmetic certificate for class 68).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate68`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate68` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.74 (Arithmetic certificate for class 69).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate69`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate69` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.75 (Arithmetic certificate for class 70).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate70`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate70` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.76 (Arithmetic certificate for class 71).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate71`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate71` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.77 (Arithmetic certificate for class 72).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate72`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate72` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.78 (Arithmetic certificate for class 73).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate73`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate73` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.79 (Arithmetic certificate for class 74).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate74`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate74` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.80 (Arithmetic certificate for class 75).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate75`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate75` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.81 (Arithmetic certificate for class 76).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate76`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate76` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.82 (Arithmetic certificate for class 77).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate77`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate77` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.83 (Arithmetic certificate for class 78).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate78`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate78` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.84 (Arithmetic certificate for class 79).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate79`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate79` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.85 (Arithmetic certificate for class 80).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate80`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate80` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.86 (Arithmetic certificate for class 81).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate81`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate81` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.87 (Arithmetic certificate for class 82).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate82`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate82` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.88 (Arithmetic certificate for class 83).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate83`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate83` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.89 (Arithmetic certificate for class 84).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate84`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate84` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.90 (Arithmetic certificate for class 85).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate85`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate85` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.91 (Arithmetic certificate for class 86).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate86`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate86` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.92 (Arithmetic certificate for class 87).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate87`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate87` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.93 (Arithmetic certificate for class 88).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate88`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate88` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.94 (Arithmetic certificate for class 89).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate89`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate89` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.95 (Arithmetic certificate for class 90).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate90`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate90` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.96 (Arithmetic certificate for class 91).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate91`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate91` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.97 (Arithmetic certificate for class 92).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate92`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate92` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.98 (Arithmetic certificate for class 93).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate93`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate93` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.99 (Arithmetic certificate for class 94).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate94`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate94` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

**Definition 1.100 (Arithmetic certificate for class 95).**

Lean statement: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate95`

*Formalization.* `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate95` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.Holes`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate0`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate1`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate10`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate11`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate12`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate13`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate14`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate15`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate16`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate17`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate18`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate19`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate2`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate20`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate21`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate22`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate23`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate24`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate25`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate26`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate27`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate28`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate29`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate3`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate30`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate31`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate32`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate33`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate34`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate35`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate36`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate37`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate38`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate39`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate4`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate40`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate41`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate42`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate43`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate44`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate45`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate46`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate47`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate48`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate49`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate5`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate50`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate51`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate52`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate53`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate54`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate55`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate56`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate57`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate58`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate59`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate6`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate60`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate61`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate62`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate63`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate64`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate65`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate66`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate67`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate68`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate69`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate7`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate70`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate71`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate72`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate73`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate74`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate75`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate76`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate77`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate78`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate79`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate8`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate80`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate81`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate82`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate83`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate84`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate85`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate86`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate87`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate88`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate89`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate9`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate90`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate91`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate92`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate93`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate94`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate95`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.globalCover`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.result`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203ConditionalCapacity.uniform_hole_bound`
- Dependency: [D5/S3/Arith/Covering/Erdos203CapacityCertificate](Erdos203CapacityCertificate.md)
- Dependency: [D5/S3/Arith/Covering/Erdos203SeventhCapacity](Erdos203SeventhCapacity.md)
