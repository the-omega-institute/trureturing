# Thin Checkerboard of Side Seventeen

## Abstract

The odd-parity class of the 17 by 17 integer grid has no-three-in-line optimum 26.

**Definition 1.1 (Integer lattice points).**

$$\operatorname{Point} = \mathbb{Z} \times \mathbb{Z}$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Point abbreviates Prod Int Int; its two coordinates are integers.

**Definition 1.2 (Integer line equations).**

$$\operatorname{LineKey} = \mathbb{Z} \times (\mathbb{Z} \times \mathbb{Z})$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.LineKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LineKey abbreviates Prod Int (Prod Int Int). The nested pair (a,(b,c)) represents a*x+b*y=c; properness is proved privately for every certificate line.

**Definition 1.3 (Displacement determinant).**

$$\forall p , q , r : \operatorname{Point}, \operatorname{det}\left(p, q, r\right) = (q_{1} - p_{1}) \cdot (r_{2} - p_{2}) - (q_{2} - p_{2}) \cdot (r_{1} - p_{1})$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.det` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression is the integer determinant of q-p and r-p, exactly as in GICT Theorem 3.4.16. Subscripts denote the first and second integer coordinates.

**Definition 1.4 (Odd-parity grid membership).**

$$\forall p : \operatorname{Point}, \operatorname{Thin}\left(p\right) \iff (0 \leq p_{1} \land p_{1} \leq 16 \land 0 \leq p_{2} \land p_{2} \leq 16 \land \operatorname{intMod}\left(p_{1} + p_{2}, 2\right) = 1)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.Thin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both coordinates lie between zero and sixteen. intMod denotes Lean integer remainder, so the last equality expresses odd coordinate sum.

**Definition 1.5 (All-slopes no-three-in-line).**

$$\forall S : \operatorname{Finset}\left(\operatorname{Point}\right), \operatorname{NTIL}\left(S\right) \iff (\forall p \in S, \forall q \in S, \forall r \in S, p \ne q \Rightarrow p \ne r \Rightarrow q \ne r \Rightarrow \operatorname{det}\left(p, q, r\right) \ne 0)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.NTIL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate ranges over every ordered triple of members and requires nonzero integer determinant whenever the three points are pairwise distinct. It imposes no restriction on slopes.

**Definition 1.6 (Integer line incidence).**

$$\forall p : \operatorname{Point}, \forall l : \operatorname{LineKey}, \operatorname{onLine}\left(p, l\right) \iff \operatorname{fst}\left(l\right) \cdot p_{1} + \operatorname{fst}\left(\operatorname{snd}\left(l\right)\right) \cdot p_{2} = \operatorname{snd}\left(\operatorname{snd}\left(l\right)\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.onLine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fst and snd are product projections. Incidence is the displayed integer equation, with no geometric Collinear predicate involved.

**Definition 1.7 (The explicit point certificate).**

$$\operatorname{witness} : \operatorname{Finset}\left(\operatorname{Point}\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining finite set is the fixed list of 26 integer points in the Lean source, copied unchanged from the preregistered certificate. It is kernel-decided finite data; the three following theorems check cardinality, thin membership, and all distinct triples. The entries are not duplicated in this mirror.

**Definition 1.8 (The weighted line certificate).**

$$\operatorname{weightedLines} : \operatorname{List}\left(\operatorname{LineKey} \times \mathbb{N}\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weightedLines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining list contains the fixed 40 pairs of integer line coefficients and natural weights from the preregistered certificate, unchanged. These are kernel-decided finite data, not an assumed optimizer output. The entries are not duplicated here; the weights sum to 320 and the required coverage scale is 24.

**Theorem 1.9 (The witness has 26 points).**

$$\operatorname{card}\left(\operatorname{witness}\right) = 26$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction counts 26 distinct points.

**Theorem 1.10 (Every witness point is thin).**

$$\forall p \in \operatorname{witness}, \operatorname{Thin}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_thin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction checks the coordinate bounds and odd parity for all 26 entries.

**Theorem 1.11 (Every distinct witness triple is noncollinear).**

$$\operatorname{NTIL}\left(\operatorname{witness}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_ntil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction verifies every distinct ordered triple; equivalently all 2600 unordered triples have nonzero determinant. No native_decide is used.

**Definition 1.12 (Line at a certificate index).**

$$\forall i : \operatorname{Fin}\left(40\right), \operatorname{line}\left(i\right) = \operatorname{fst}\left(\operatorname{get}\left(\operatorname{weightedLines}, \operatorname{val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.line` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

get is zero-based list lookup at val(i). Lean transports i from Fin 40 to Fin weightedLines.length using the kernel-checked length equality before taking the first projection.

**Definition 1.13 (Weight at a certificate index).**

$$\forall i : \operatorname{Fin}\left(40\right), \operatorname{weight}\left(i\right) = \operatorname{snd}\left(\operatorname{get}\left(\operatorname{weightedLines}, \operatorname{val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same zero-based lookup and length transport is followed by the second projection, yielding a natural number.

**Definition 1.14 (Total incident line weight).**

$$\forall p : \operatorname{Point}, \operatorname{cover}\left(p\right) = \sum_{i : \operatorname{Fin}\left(40\right)} \operatorname{ite}\left(\operatorname{onLine}\left(p, \operatorname{line}\left(i\right)\right), \operatorname{weight}\left(i\right), 0\right)$$

*Formalization.* `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.cover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is over all forty indices and takes natural values. ite(P,a,b) equals a when P holds and b otherwise.

**Theorem 1.15 (Total certificate weight).**

$$\sum_{i : \operatorname{Fin}\left(40\right)} \operatorname{weight}\left(i\right) = 320$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean kernel checks the sum of the forty natural weights.

**Theorem 1.16 (Every thin grid point has coverage at least 24).**

$$\forall x , y : \operatorname{Fin}\left(17\right), \operatorname{natMod}\left(\operatorname{val}\left(x\right) + \operatorname{val}\left(y\right), 2\right) = 1 \Rightarrow 24 \leq \operatorname{cover}\left((\operatorname{ofNat}\left(\operatorname{val}\left(x\right)\right), \operatorname{ofNat}\left(\operatorname{val}\left(y\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.cover_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

val maps Fin 17 to the naturals, natMod denotes natural remainder, and ofNat explicitly embeds each coordinate into the integers before cover is applied. Kernel enumeration checks the whole 17 by 17 grid under its parity premise.

**Theorem 1.17 (Every admissible set has at most 26 points).**

$$\forall S : \operatorname{Finset}\left(\operatorname{Point}\right), (\forall p \in S, \operatorname{Thin}\left(p\right)) \Rightarrow \operatorname{NTIL}\left(S\right) \Rightarrow \operatorname{card}\left(S\right) \leq 26$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A proper integer line carries at most two points of an NTIL set. Double counting weighted incidences therefore gives 24*card(S) <= 2*320 = 640, and natural arithmetic yields card(S) <= 26.

**Theorem 1.18 (Exact optimum: attainment and universal bound).**

$$(\exists S : \operatorname{Finset}\left(\operatorname{Point}\right), (\forall p \in S, \operatorname{Thin}\left(p\right)) \land \operatorname{card}\left(S\right) = 26 \land \operatorname{NTIL}\left(S\right)) \land (\forall T : \operatorname{Finset}\left(\operatorname{Point}\right), (\forall p \in T, \operatorname{Thin}\left(p\right)) \Rightarrow \operatorname{NTIL}\left(T\right) \Rightarrow \operatorname{card}\left(T\right) \leq 26)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.thinCheckerboard17_ntil_max_eq_26` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GICT Theorem 3.4.16 is mirrored as one conjunction: an admissible 26-point set exists and every admissible set has at most 26 points. Both preregistered escape certificates from Remark 3.4.17 are live in the proof; the remark is not claimed as covered. This exact finite result is derived in this repository. Prellberg, arXiv:2605.09215, Definition 2, Table 1, and Section 4 supply the problem context: Table 1 gives exact thin-checkerboard maxima through n=16, ending at 24. The present claim is only for n=17 and its odd-parity class. It asserts neither a result for other n nor a bridge to Mathlib Collinear, and makes no global novelty claim.

## References

- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.LineKey`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.NTIL`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.Point`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.Thin`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.cover`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.cover_grid`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.det`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.line`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.onLine`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.thinCheckerboard17_ntil_max_eq_26`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.upper_bound`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weight`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weight_sum`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.weightedLines`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_card`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_ntil`
- Truth anchor: `D5/S3/Arith/Lattices/ThinCheckerboardNoThreeInLineSeventeen.witness_thin`
