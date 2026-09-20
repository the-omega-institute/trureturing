# Flórez--Junes--Ramírez Cubic-Lattice Plane-Path Counts

## Abstract

Both printed plane-count conjectures fail at path length three.

**Definition 1.1 (Signed coordinate steps).**

$$Step = \operatorname{Fin}\left(3\right) \times \mathrm{Bool}$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.Step` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

A step chooses one of the three coordinate axes and one of two signs. The Fin(3) values 0, 1, and 2 represent the printed axes 1, 2, and 3; the Boolean component represents the sign.

**Definition 1.2 (Paths from the origin).**

$$\forall k \in \mathrm{Nat},\; \operatorname{Path}\left(k\right) = \left(\operatorname{Fin}\left(k\right) \to Step\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.Path` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

A path of length k is a sequence of k signed coordinate steps. Its initial vertex is the origin, as in the source definition.

**Definition 1.3 (Initial-subpath coordinate vector).**

$$\forall k \in \mathrm{Nat},\; \forall P \in \operatorname{Path}\left(k\right),\; \forall r \in \mathrm{Nat},\; \operatorname{partialSum}\left(P, r\right) = (\lambda c: \operatorname{Fin}\left(3\right) \mapsto \sum_{i: \operatorname{Fin}\left(k\right)} \operatorname{ite}\left((\operatorname{val}\left(i\right) < r) \land (\operatorname{fst}\left(P\left(i\right)\right) = c), \operatorname{ite}\left(\operatorname{snd}\left(P\left(i\right)\right), 1, -1\right), 0\right))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.partialSum` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

For an axis c, partialSum(P,r)(c) sums the signed contributions on c from exactly those step indices i with i < r. This is the source vector V_r.

**Definition 1.4 (The printed C-three-plus predicate).**

$$\forall k \in \mathrm{Nat},\; \forall P \in \operatorname{Path}\left(k\right),\; (\operatorname{InCThreePlus}\left(P\right)) \Leftrightarrow ((\forall r \in \operatorname{Fin}\left(k + 1\right),\; (0 < \operatorname{val}\left(r\right)) \Rightarrow (0 \le \operatorname{partialSum}\left(P, \operatorname{val}\left(r\right), 2\right))) \land (\operatorname{partialSum}\left(P, k, 2\right) = 0))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InCThreePlus` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The third coordinate is nonnegative after every nonempty prefix and is zero after the complete path. A binder r : Fin(k+1), together with 0 < val(r), ranges over exactly the printed indices 0 < r <= k.

**Definition 1.5 (Complete containment in the xz-plane).**

$$\forall k \in \mathrm{Nat},\; \forall P \in \operatorname{Path}\left(k\right),\; (\operatorname{InXzPlane}\left(P\right)) \Leftrightarrow (\forall r \in \operatorname{Fin}\left(k + 1\right),\; (0 < \operatorname{val}\left(r\right)) \Rightarrow (\operatorname{partialSum}\left(P, \operatorname{val}\left(r\right), 1\right) = 0))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InXzPlane` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

Every noninitial vertex has second coordinate zero. The omitted initial vertex is the origin and therefore already lies in the xz-plane.

**Definition 1.6 (Complete containment in the yz-plane).**

$$\forall k \in \mathrm{Nat},\; \forall P \in \operatorname{Path}\left(k\right),\; (\operatorname{InYzPlane}\left(P\right)) \Leftrightarrow (\forall r \in \operatorname{Fin}\left(k + 1\right),\; (0 < \operatorname{val}\left(r\right)) \Rightarrow (\operatorname{partialSum}\left(P, \operatorname{val}\left(r\right), 0\right) = 0))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InYzPlane` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

Every noninitial vertex has first coordinate zero. The omitted initial vertex is the origin and therefore already lies in the yz-plane.

**Definition 1.7 (Decidability of C-three-plus membership).**

$$\forall k \in \mathrm{Nat},\; \operatorname{DecidablePred}\left((\lambda P: \operatorname{Path}\left(k\right) \mapsto \operatorname{InCThreePlus}\left(P\right))\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInCThreePlus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

This instance unfolds InCThreePlus once so finite universal quantification can be decided. It changes no truth value.

**Definition 1.8 (Decidability of xz-plane containment).**

$$\forall k \in \mathrm{Nat},\; \operatorname{DecidablePred}\left((\lambda P: \operatorname{Path}\left(k\right) \mapsto \operatorname{InXzPlane}\left(P\right))\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInXzPlane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

This instance unfolds InXzPlane once so finite universal quantification can be decided. It changes no truth value.

**Definition 1.9 (Decidability of yz-plane containment).**

$$\forall k \in \mathrm{Nat},\; \operatorname{DecidablePred}\left((\lambda P: \operatorname{Path}\left(k\right) \mapsto \operatorname{InYzPlane}\left(P\right))\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInYzPlane` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

This instance unfolds InYzPlane once so finite universal quantification can be decided. It changes no truth value.

**Definition 1.10 (The printed-reading xz-plane count).**

$$\forall k \in \mathrm{Nat},\; \operatorname{xzCount}\left(k\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Path}\left(k\right)\right), (\lambda P: \operatorname{Path}\left(k\right) \mapsto (\operatorname{InCThreePlus}\left(P\right)) \land (\operatorname{InXzPlane}\left(P\right)))\right)\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.xzCount` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The count is the cardinality of the full finite path space filtered by both InCThreePlus and InXzPlane.

**Definition 1.11 (The printed-reading yz-plane count).**

$$\forall k \in \mathrm{Nat},\; \operatorname{yzCount}\left(k\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Path}\left(k\right)\right), (\lambda P: \operatorname{Path}\left(k\right) \mapsto (\operatorname{InCThreePlus}\left(P\right)) \land (\operatorname{InYzPlane}\left(P\right)))\right)\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.yzCount` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The count is the cardinality of the full finite path space filtered by both InCThreePlus and InYzPlane.

**Definition 1.12 (The printed binomial sum).**

$$\forall k \in \mathrm{Nat},\; \operatorname{formula}\left(k\right) = \sum_{i \in \operatorname{Icc}\left(1, k + 1\right)} \operatorname{NatDiv}\left(\operatorname{binom}\left(2 \cdot i, i\right) \cdot \operatorname{binom}\left(k, i - 1\right), i + 1\right)$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.formula` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The index set is the inclusive interval from 1 through k+1. The function binom(n,j) denotes Nat.choose(n,j), and NatDiv denotes natural-number integer division. Each displayed division is exact by the central-binomial divisibility identity.

**Definition 1.13 (Conjecture 1 as printed).**

$$(claim1) \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\operatorname{xzCount}\left(k\right) = \operatorname{formula}\left(k\right)))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim1` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The paper states: "Conjecture 1: For k ≥ 1, the number of paths in C_3^+(k) that are completely contained in the xz-plane is (see Table 4 first line) Σ_{i=1}^{k+1} \binom{2i}{i}\binom{k}{i−1}/(i+1)."

**Definition 1.14 (Conjecture 2 as printed).**

$$(claim2) \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\operatorname{yzCount}\left(k\right) = \operatorname{formula}\left(k\right)))$$

*Formalization.* `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim2` (`✓ std3`).

*Citation.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

The paper states: "Conjecture 2: For k ≥ 1, the number of paths in C_3^+(k) that are completely contained in the yz-plane is Σ_{i=1}^{k+1} \binom{2i}{i}\binom{k}{i−1}/(i+1)."

**Theorem 1.15 (Conjecture 1 is false).**

$$\neg claim1$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

At k = 3, the printed xz-plane predicate selects 14 of the 216 signed three-step paths, while the printed formula equals 36. Hence the universal claim is false.

**Theorem 1.16 (Conjecture 2 is false).**

$$\neg claim2$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rigoberto Flórez, Leandro Junes, José L. Ramírez (2018). *Further Results on Paths in an n-Dimensional Cubic Lattice*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf>.

*Commentary.*

At k = 3, the printed yz-plane predicate selects 14 of the 216 signed three-step paths, while the printed formula equals 36. Hence the universal claim is false.

## References

- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InCThreePlus`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InXzPlane`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.InYzPlane`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.Path`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.Step`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim1`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim2`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.formula`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInCThreePlus`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInXzPlane`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.instDecidablePredInYzPlane`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.partialSum`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result1`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result2`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.xzCount`
- Truth anchor: `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.yzCount`
