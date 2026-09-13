# Simic H-655(ii) weighted power-sum floor identity

## Abstract

Simic's weighted power-sum floor identity for at least two positive indices.

**Theorem 1.1 (The weighted power-sum floor identity).**

$$\forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; ((2 \le Finset.card\left(s\right)) \Rightarrow (((\forall i \in \mathbb{N},\; (i \in s) \Rightarrow (1 \le i)) \Rightarrow (\forall q \in \mathbb{N},\; ((2 \le q) \Rightarrow (\left\lfloor\frac{\left((q : \mathbb{Q}) - 1\right) \cdot \sum_{i \in s} (i : \mathbb{Q}) \cdot (q : \mathbb{Q})^{i}}{\sum_{i \in s} (q : \mathbb{Q})^{i}}\right\rfloor = (Finset.max\left(s\right) : \mathbb{Z}) \cdot \left((q : \mathbb{Z}) - 1\right) - 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity.simic_h655_ii` (`✓ std3`). ∎

*Citation.* Slavko Simic (2007). *Problem H-655, The Fibonacci Quarterly 45(2)*. URL: <https://www.fq.math.ca/Problems/Aug2009advanced.pdf>.

*Commentary.*

For a finite set of distinct positive natural indices with at least two members and a natural base at least two, the integer floor of the weighted power mean after multiplication by q minus one is one below the maximum-index multiple. Lean's Finset.max' supplies the maximum after its nonemptiness proof. The proof centers at the maximum index: a second index makes the deficit positive, while the closed tail identity and subset domination bound it by one. The singleton endpoint has floor c(q - 1), so it is outside this statement. Part 1 of the printed problem is not formalized.

## References

- Truth anchor: `D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity.simic_h655_ii`
