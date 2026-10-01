# The period of hard-square necklaces

## Abstract

Adamaszek's necklace transformation combines simultaneous jumps, vector changes, and corrections at facing gaps of length three. Every legal necklace on an even circle returns to its isometry class after n−3k steps. Compressing a lifted stone at x with index i and signed vector v to y=2x+v−3i turns collisions into exchanges of unit velocities. After half the compressed circumference, both velocity classes have shifted equally; winding and parity recover the physical vectors and positions.

**Definition 1.1 (Stone vectors).**

$$\operatorname{Vec} = \left\{\operatorname{negTwo}, \operatorname{negOne}, \operatorname{posOne}, \operatorname{posTwo}\right\}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Vec` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"We define a (k, n)-necklace. It is a collection of 2k points (stones) distributed along the circumference of a circle of length n, together with an assignment of a number from {−2, −1, 1, 2} to each of the stones." (p. 12). The four constructors encode the four signed vectors in the stated order.

**Definition 1.2 (Vector −2).**

$$\operatorname{negTwo} \in \operatorname{Vec}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negTwo` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

This constructor is the indicated signed stone vector.

**Definition 1.3 (Vector −1).**

$$\operatorname{negOne} \in \operatorname{Vec}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negOne` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

This constructor is the indicated signed stone vector.

**Definition 1.4 (Vector 1).**

$$\operatorname{posOne} \in \operatorname{Vec}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.posOne` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

This constructor is the indicated signed stone vector.

**Definition 1.5 (Vector 2).**

$$\operatorname{posTwo} \in \operatorname{Vec}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.posTwo` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

This constructor is the indicated signed stone vector.

**Definition 1.6 (Signed displacement).**

$$\forall v \in \operatorname{Vec},\; \operatorname{value}\left(v\right) = \operatorname{ite}\left((v = \operatorname{negTwo}), -2, \operatorname{ite}\left((v = \operatorname{negOne}), -1, \operatorname{ite}\left((v = \operatorname{posOne}), 1, 2\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.value` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"The vector points 1 or 2 units clockwise (positive value) or anti-clockwise (negative value) from each stone and we say a stone faces the direction of its vector." (p. 12). value is the signed integer displacement.

**Definition 1.7 (Vector length).**

$$\forall v \in \operatorname{Vec},\; \operatorname{length}\left(v\right) = \operatorname{ite}\left((v = \operatorname{negTwo}), 2, \operatorname{ite}\left((v = \operatorname{negOne}), 1, \operatorname{ite}\left((v = \operatorname{posOne}), 1, 2\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.length` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

The length is the absolute value of the signed vector, either one or two.

**Definition 1.8 (Clockwise direction).**

$$\forall v \in \operatorname{Vec},\; \operatorname{positive}\left(v\right) \Leftrightarrow ((v = \operatorname{posOne}) \lor (v = \operatorname{posTwo}))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.positive` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

A vector is positive exactly for the two clockwise constructors posOne and posTwo.

**Definition 1.9 (TURN).**

$$\forall v \in \operatorname{Vec},\; \operatorname{turn}\left(v\right) = \operatorname{ite}\left((v = \operatorname{negTwo}), \operatorname{posOne}, \operatorname{ite}\left((v = \operatorname{negOne}), \operatorname{posTwo}, \operatorname{ite}\left((v = \operatorname{posOne}), \operatorname{negTwo}, \operatorname{negOne}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.turn` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"(TURN) all stone vectors change according to the rule −2→1, −1→2, 1→−2, 2→−1," (p. 13). Both the direction and the length switch to the other option.

**Definition 1.10 (Reflection of a vector).**

$$\forall v \in \operatorname{Vec},\; \operatorname{negate}\left(v\right) = \operatorname{ite}\left((v = \operatorname{negTwo}), \operatorname{posTwo}, \operatorname{ite}\left((v = \operatorname{negOne}), \operatorname{posOne}, \operatorname{ite}\left((v = \operatorname{posOne}), \operatorname{negOne}, \operatorname{negTwo}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negate` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

A reflection reverses the tangent direction and preserves the vector length.

**Definition 1.11 (Length correction).**

$$\forall v \in \operatorname{Vec},\; \operatorname{shorten}\left(v\right) = \operatorname{ite}\left((v = \operatorname{negTwo}), \operatorname{negOne}, \operatorname{ite}\left((v = \operatorname{negOne}), \operatorname{negOne}, \operatorname{ite}\left((v = \operatorname{posOne}), \operatorname{posOne}, \operatorname{posOne}\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.shorten` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"(FIX) if any two stones find themselves in distance 3 facing each other and any of their vectors has length 2, then adjust the offending vectors by reducing their length to 1." (p. 13). shorten preserves direction and reduces length two to one, leaving length one unchanged.

**Definition 1.12 (Configurations on the integer circle).**

$$\forall n \in \mathbb{N},\; \operatorname{Config}\left(n\right) = \left(\operatorname{ZMod}\left(n\right) \to \operatorname{Option}\left(\operatorname{Vec}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Config` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"We define a (k, n)-necklace. It is a collection of 2k points (stones) distributed along the circumference of a circle of length n, together with an assignment of a number from {−2, −1, 1, 2} to each of the stones." (p. 12). Each site of ZMod n carries either no stone or one of the four vectors. The pair conditions force every consecutive distance to be integral, so rotation of the origin places all stones at integer sites.

**Definition 1.13 (Occupied sites).**

$$\forall n \in \mathbb{N},\; \forall N \in \operatorname{Config}\left(n\right),\; \forall p \in \operatorname{ZMod}\left(n\right),\; \operatorname{HasStone}\left(n, N, p\right) \Leftrightarrow (\exists v \in \operatorname{Vec},\; N\left(p\right) = \operatorname{some}\left(v\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.HasStone` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

A site is occupied exactly when its optional vector is some v for a stone vector v.

**Definition 1.14 (Clockwise distance).**

$$\forall n \in \mathbb{N},\; \forall p \in \operatorname{ZMod}\left(n\right),\; \forall q \in \operatorname{ZMod}\left(n\right),\; \operatorname{clockwiseDistance}\left(n, p, q\right) = \operatorname{val}\left(q - p\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.clockwiseDistance` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

val denotes ZMod.val: the representative in {0,…,n−1} when n is positive. The clockwise distance is val(q−p). The formula uses a natural-valued distance, not a real fraction.

**Definition 1.15 (Cyclically consecutive stones).**

$$\forall n \in \mathbb{N},\; \forall N \in \operatorname{Config}\left(n\right),\; \forall p \in \operatorname{ZMod}\left(n\right),\; \forall q \in \operatorname{ZMod}\left(n\right),\; \operatorname{Consecutive}\left(n, N, p, q\right) \Leftrightarrow ((p \ne q) \land ((\operatorname{HasStone}\left(n, N, p\right)) \land ((\operatorname{HasStone}\left(n, N, q\right)) \land (\forall r \in \operatorname{ZMod}\left(n\right),\; (0 < \operatorname{clockwiseDistance}\left(n, p, r\right)) \Rightarrow ((\operatorname{clockwiseDistance}\left(n, p, r\right) < \operatorname{clockwiseDistance}\left(n, p, q\right)) \Rightarrow (N\left(r\right) = \operatorname{none}))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Consecutive` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

Two distinct occupied sites are consecutive when the open clockwise arc between them is empty. This also includes the pair crossing the chosen origin.

**Definition 1.16 (The four pair conditions).**

$$\forall d \in \mathbb{Z},\; \forall v \in \operatorname{Vec},\; \forall w \in \operatorname{Vec},\; \operatorname{PairAdmissible}\left(d, v, w\right) \Leftrightarrow ((0 < d) \land ((\operatorname{positive}\left(v\right) \Leftrightarrow (\neg (\operatorname{positive}\left(w\right)))) \land (((\neg (\operatorname{positive}\left(v\right))) \Rightarrow ((\operatorname{positive}\left(w\right)) \Rightarrow (\operatorname{Odd}\left(d\right)))) \land (((\operatorname{positive}\left(v\right)) \Rightarrow ((\neg (\operatorname{positive}\left(w\right))) \Rightarrow (\operatorname{Odd}\left(d + \operatorname{length}\left(v\right) + \operatorname{length}\left(w\right)\right)))) \land ((\operatorname{positive}\left(v\right)) \Rightarrow ((\neg (\operatorname{positive}\left(w\right))) \Rightarrow ((3 \le d) \land ((d = 3) \Rightarrow ((\operatorname{length}\left(v\right) = 1) \land (\operatorname{length}\left(w\right) = 1))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.PairAdmissible` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"consecutive stones face in opposite directions," (p. 12); "if two consecutive stones face away from each other then their distance is an odd integer," "if two consecutive stones face towards each other then their distance plus the lengths of their vectors is an odd integer," and "if two consecutive stones face towards each other then their distance is at least 3; moreover if their distance is exactly 3 then their vectors have length 1." (p. 13). ofNat denotes Int.ofNat, the canonical coercion from naturals to integers. d is the positive clockwise gap in integers, v the left vector, and w the right vector. Left negative and right positive means facing away; left positive and right negative means facing towards.

**Definition 1.17 (Legal necklaces).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall N \in \operatorname{Config}\left(n\right),\; \operatorname{IsNecklace}\left(n, k, N\right) \Leftrightarrow ((0 < n) \land ((\exists S \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{card}\left(S\right) = 2 \cdot k) \land (\forall p \in \operatorname{ZMod}\left(n\right),\; p \in S \Leftrightarrow (\operatorname{HasStone}\left(n, N, p\right)))) \land (\forall p \in \operatorname{ZMod}\left(n\right),\; \forall q \in \operatorname{ZMod}\left(n\right),\; \forall v \in \operatorname{Vec},\; \forall w \in \operatorname{Vec},\; (\operatorname{Consecutive}\left(n, N, p, q\right)) \Rightarrow ((N\left(p\right) = \operatorname{some}\left(v\right)) \Rightarrow ((N\left(q\right) = \operatorname{some}\left(w\right)) \Rightarrow (\operatorname{PairAdmissible}\left(\operatorname{ofNat}\left(\operatorname{clockwiseDistance}\left(n, p, q\right)\right), v, w\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.IsNecklace` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"We define a (k, n)-necklace. It is a collection of 2k points (stones) distributed along the circumference of a circle of length n, together with an assignment of a number from {−2, −1, 1, 2} to each of the stones." (p. 12). "We identify (k, n)-necklaces which differ by an isometry of the circle." (p. 13). IsNecklace includes positivity of n, exactly 2k occupied sites, and all four conditions for every cyclically consecutive pair. The global even-n and positive-k conventions occur in claim.

**Definition 1.18 (Simultaneous JUMP and TURN).**

$$\forall n \in \mathbb{N},\; \forall N \in \operatorname{Config}\left(n\right),\; \forall q \in \operatorname{ZMod}\left(n\right),\; \operatorname{jumpTurn}\left(n, N\right)\left(q\right) = \operatorname{ite}\left((\exists a \in \operatorname{ZMod}\left(n\right)\times\operatorname{Vec},\; (N\left(\operatorname{fst}\left(a\right)\right) = \operatorname{some}\left(\operatorname{snd}\left(a\right)\right)) \land (q = \operatorname{fst}\left(a\right) + (\operatorname{cast}\left(\operatorname{value}\left(\operatorname{snd}\left(a\right)\right)\right) : \operatorname{ZMod}\left(n\right)))), \operatorname{some}\left(\operatorname{turn}\left(\operatorname{snd}\left(\operatorname{choose}\left((\exists a \in \operatorname{ZMod}\left(n\right)\times\operatorname{Vec},\; (N\left(\operatorname{fst}\left(a\right)\right) = \operatorname{some}\left(\operatorname{snd}\left(a\right)\right)) \land (q = \operatorname{fst}\left(a\right) + (\operatorname{cast}\left(\operatorname{value}\left(\operatorname{snd}\left(a\right)\right)\right) : \operatorname{ZMod}\left(n\right))))\right)\right)\right)\right), \operatorname{none}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.jumpTurn` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"(JUMP) all stones jump as dictated by their vectors," (p. 13). cast denotes Int.cast, with its target ZMod n displayed explicitly. For the existential E displayed below, choose(E) means its chosen witness; fst and snd are its position and vector. A destination with an incoming stone receives its turned vector. On legal necklaces the inflow is unique; choice totalizes the function on illegal configurations.

**Definition 1.19 (Simultaneous FIX).**

$$\forall n \in \mathbb{N},\; \forall M \in \operatorname{Config}\left(n\right),\; \forall p \in \operatorname{ZMod}\left(n\right),\; ((M\left(p\right) = \operatorname{none}) \Rightarrow (\operatorname{fix}\left(n, M\right)\left(p\right) = \operatorname{none})) \land (\forall v \in \operatorname{Vec},\; (M\left(p\right) = \operatorname{some}\left(v\right)) \Rightarrow (\operatorname{fix}\left(n, M\right)\left(p\right) = \operatorname{ite}\left((\operatorname{ite}\left((\operatorname{positive}\left(v\right)), (\exists w \in \operatorname{Vec},\; (M\left(p + 3\right) = \operatorname{some}\left(w\right)) \land (\neg (\operatorname{positive}\left(w\right)))), (\exists w \in \operatorname{Vec},\; (M\left(p - 3\right) = \operatorname{some}\left(w\right)) \land (\operatorname{positive}\left(w\right)))\right)), \operatorname{some}\left(\operatorname{shorten}\left(v\right)\right), \operatorname{some}\left(v\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.fix` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"(FIX) if any two stones find themselves in distance 3 facing each other and any of their vectors has length 2, then adjust the offending vectors by reducing their length to 1." (p. 13). All tests read the same post-JUMP, post-TURN configuration. ite(P,a,b) means a when P holds and b otherwise. A clockwise vector tests p+3 for a negative vector; an anticlockwise vector tests p−3 for a positive vector. Length-one vectors are unaffected by shorten.

**Definition 1.20 (The necklace transformation).**

$$\forall n \in \mathbb{N},\; \forall N \in \operatorname{Config}\left(n\right),\; \operatorname{necklaceT}\left(n, N\right) = \operatorname{fix}\left(n, \operatorname{jumpTurn}\left(n, N\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.necklaceT` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"Next we describe a necklace transformation T which takes a (k, n)-necklace and performs the following operations:" (p. 13). necklaceT applies JUMP and TURN simultaneously, followed by FIX.

**Definition 1.21 (Action on configurations).**

$$\forall n \in \mathbb{N},\; \forall g \in \operatorname{DihedralGroup}\left(n\right),\; \forall c \in \operatorname{ZMod}\left(n\right),\; \forall N \in \operatorname{Config}\left(n\right),\; \forall q \in \operatorname{ZMod}\left(n\right),\; ((g = \operatorname{r}\left(c\right)) \Rightarrow (\operatorname{circleIsometryAct}\left(n, g, N\right)\left(q\right) = N\left(q - c\right))) \land ((g = \operatorname{sr}\left(c\right)) \Rightarrow (\operatorname{circleIsometryAct}\left(n, g, N\right)\left(q\right) = \operatorname{map}\left(\operatorname{negate}, N\left(-q + c\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.circleIsometryAct` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

Mathlib DihedralGroup n supplies rotations r(c) and reflections sr(c), whose forward point maps are q↦q+c and q↦−q+c. The action pulls a configuration back through the inverse point isometry; reflection also negates its vector. Option.map leaves none unchanged and applies negate to a present vector.

**Definition 1.22 (The isometry action instance).**

$$\forall n \in \mathbb{N},\; \forall g \in \operatorname{DihedralGroup}\left(n\right),\; \forall N \in \operatorname{Config}\left(n\right),\; \operatorname{smul}\left(\operatorname{circleIsometrySMul}\left(n\right), g, N\right) = \operatorname{circleIsometryAct}\left(n, g, N\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.circleIsometrySMul` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

The explicitly named SMul instance has smul equal to circleIsometryAct. Multiplication g•N in claim uses this instance.

**Definition 1.23 (Conjecture 7.4).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\operatorname{Even}\left(n\right)) \Rightarrow ((1 \le k) \Rightarrow (\forall N \in \operatorname{Config}\left(n\right),\; (\operatorname{IsNecklace}\left(n, k, N\right)) \Rightarrow (\exists g \in \operatorname{DihedralGroup}\left(n\right),\; \operatorname{iterate}\left(\operatorname{necklaceT}\left(n\right), n - 3 \cdot k\right)\left(N\right) = g \cdot N))))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.claim` (`✓ std3`).

*Citation.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

"The length of every cycle in the graph Neck(k, n) divides n−3k. In other words, for every (k, n)-necklace N we have Tⁿ⁻³ᵏN = N." (Conjecture 7.4, p. 14). n is an even positive circle length and k≥1 counts half the stones. Config n, IsNecklace k N, and the rotation/reflection action encode the source's objects and identification. The exponent is natural subtraction n−3k; the proof derives 4k≤n from the pair conditions. iterate denotes Function.iterate; iterate(T,0) is the identity function.

**Theorem 1.24 (Proof of Conjecture 7.4).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result` (`✓ std3`). ∎

*Resolves.* `Problems/adamaszek-2012-necklace-cycle-length` (proved) by `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"adamaszek-2012-necklace-cycle-length","declaration_gid":"D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michal Adamaszek (2012). *Hard squares on cylinders revisited*. URL: <https://arxiv.org/abs/1202.1655v2>.

*Commentary.*

Sort the physical stones and extend their coordinates periodically to integers. The compressed positions yᵢ=2xᵢ+vᵢ−3i are strictly ordered, with circumference 2(n−3k); their velocities are sign(vᵢ)(2|vᵢ|−3), hence ±1. FIX exchanges the velocities at disjoint crossing pairs, so the compressed evolution is free motion followed by relabelling. At L=n−3k steps both velocities give the same spatial displacement modulo 2L, and an increasing bijection of the integer labels is a translation. The total compressed first moment determines this label shift as minus the number of negative compressed velocities. Even physical circumference fixes its parity, allowing recovery of each physical vector and position. The final isometry is a rotation, so reflection is not needed for the return.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Config`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Consecutive`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.HasStone`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.IsNecklace`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.PairAdmissible`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.Vec`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.circleIsometryAct`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.circleIsometrySMul`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.clockwiseDistance`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.fix`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.jumpTurn`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.length`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.necklaceT`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negOne`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negTwo`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.negate`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.posOne`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.posTwo`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.positive`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.result`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.shorten`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.turn`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.value`
