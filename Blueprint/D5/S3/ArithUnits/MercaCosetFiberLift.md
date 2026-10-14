# Uniform Least-Residue Unit-Coset Lift

## Abstract

Reduction of a unit coset through a coprime prime extension of the modulus has an exact rational least-residue first moment. Two finite bijections identify retained units and removed prime multiples on native unit groups.

For every modulus n, the unit group is the actual group of invertible elements of Z/nZ, and r denotes the natural-valued ZMod.val. At positive moduli this is the least nonnegative representative. At n greater than one every unit has representative between one and n minus one. Cardinalities are finite carrier cardinalities. All moment and deviation arithmetic below is rational; the integer representative is coerced before subtraction.

**Definition 1.1 (Actual finite left cosets).**

$$\forall (n:\mathbb{N}), [\operatorname{NeZero}(n)] \forall (K:\operatorname{Subgroup}((\mathbb{Z}/n\mathbb{Z})^{\times})), \forall (c:(\mathbb{Z}/n\mathbb{Z})^{\times}), \operatorname{cosetFinset}(n, K, c) = \{ u \in (\mathbb{Z}/n\mathbb{Z})^{\times} \mid c^{-1}u \in K\}$$

*Formalization.* `D5/S3/ArithUnits/MercaCosetFiberLift.cosetFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The membership condition is c inverse times u in K, so this is the left coset cK.

**Definition 1.2 (Reduction on the actual unit groups).**

$$\forall (N:\mathbb{N}), \forall (\ell:\mathbb{N}), \operatorname{reduceUnits}(N, \ell) = \operatorname{unitsMap}(N \mid N\ell)$$

*Formalization.* `D5/S3/ArithUnits/MercaCosetFiberLift.reduceUnits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This multiplicative map is induced by reduction modulo N, using N dividing N ell. Its source is the unit group modulo N ell and its target the unit group modulo N.

**Definition 1.3 (The actual reduction preimage).**

$$\forall (N:\mathbb{N}), \forall (\ell:\mathbb{N}), [\operatorname{NeZero}(N\ell)] \forall (B:\operatorname{Finset}((\mathbb{Z}/N\mathbb{Z})^{\times})), \operatorname{liftedFinset}(N, \ell, B) = \{ v \in (\mathbb{Z}/N\ell\mathbb{Z})^{\times} \mid \operatorname{reduceUnits}(N, \ell)(v) \in B\}$$

*Formalization.* `D5/S3/ArithUnits/MercaCosetFiberLift.liftedFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lifted finite set contains exactly the units whose reduction belongs to the given set.

**Definition 1.4 (The rational least-residue moment).**

$$\forall (n:\mathbb{N}), \forall (B:\operatorname{Finset}((\mathbb{Z}/n\mathbb{Z})^{\times})), M_{n}(B) = \sum_{u \in B} r_{n}(u) \in \mathbb{Q}$$

*Formalization.* `D5/S3/ArithUnits/MercaCosetFiberLift.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each integer representative is coerced into the rationals before summing.

**Definition 1.5 (The subgroup-sized rational center).**

$$\forall (n:\mathbb{N}), \forall (K:\operatorname{Subgroup}((\mathbb{Z}/n\mathbb{Z})^{\times})), \forall (B:\operatorname{Finset}((\mathbb{Z}/n\mathbb{Z})^{\times})), F_{n}(K,B) = M_{n}(B)-\frac{n\lvert K\rvert}{2}$$

*Formalization.* `D5/S3/ArithUnits/MercaCosetFiberLift.deviation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The center uses the cardinality of the subgroup, while the finite set is an explicit argument.

**Theorem 1.6 (The complete uniform lift theorem).**

$$\forall (N:\mathbb{N}), \forall (\ell:\mathbb{N}), \forall (K:\operatorname{Subgroup}((\mathbb{Z}/N\mathbb{Z})^{\times})), \forall (c:(\mathbb{Z}/N\mathbb{Z})^{\times}), 1 < N \land \operatorname{Prime}(\ell) \land \operatorname{Coprime}(\ell, N) \Rightarrow\\{}\operatorname{let} \pi_{N,\ell} = \operatorname{reduceUnits}(N, \ell) \operatorname{in} \operatorname{let} H = \pi_{N,\ell}^{-1}(K) \operatorname{in} \operatorname{let} e = \operatorname{unitOfCoprime}(\ell) \operatorname{in} \operatorname{let} C = \operatorname{cosetFinset}(N, K, c) \operatorname{in} \operatorname{let} C' = \operatorname{cosetFinset}(N, K, e^{-1}c) \operatorname{in} \operatorname{let} L = \operatorname{liftedFinset}(N, \ell, C) \operatorname{in} \lvert H\rvert = \lvert K\rvert(\ell-1) \land\\{}\lvert L\rvert = \lvert K\rvert(\ell-1) \land\\{}(\exists d \in (\mathbb{Z}/N\ell\mathbb{Z})^{\times}, \pi_{N,\ell}(d) = c \land L = \operatorname{cosetFinset}(N\ell, H, d)) \land\\{}M_{N\ell}(L) = \ell M_{N}(C)+\frac{N\lvert K\rvert\ell(\ell-1)}{2}-\ell M_{N}(C') \land\\{}F_{N\ell}(H,L) = \ell(F_{N}(K,C)-F_{N}(K,C')) \land\\{}F_{N\ell}(H,L) = \ell(M_{N}(C)-M_{N}(C'))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaCosetFiberLift.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index all representative blocks by (u,t) in C times {0,...,ell minus one}, with q equal to r_N(u) plus Nt. The representative bound gives q below N ell, and reduction of q modulo N is u. Consequently q is coprime to N. Euclidean quotient and remainder recover the pair, proving uniqueness. For blocks not divisible by ell, q is coprime to both factors and defines a unit modulo N ell reducing to u. Conversely a lifted unit v gives (pi(v),r_(N ell)(v)/N). Its reduction representative is the remainder modulo N, so the division equation recovers q exactly. Unit coprimality excludes divisibility by ell. The two maps are mutually inverse on native unit carriers and preserve the representative weight. For removed blocks, a unit y in C prime gives z equal to ell times r_N(y). The unit ey belongs to C, its representative is z modulo N, and the block (ey,z/N) has value z. In the inverse direction, divisibility gives a equal to q/ell with ell a equal to q and a below N. Coprimality of q with N implies coprimality of a with N, so a defines a native unit y. Reducing ell a equal to q proves ey equal to u; hence y belongs to the inverse-translated coset C prime. Division and block uniqueness prove both inverse identities. The removed weight is exactly ell times r_N(y). Summing all blocks gives ell M_N(C) plus N times the size of C times ell(ell minus one)/2, with the triangular sum calculated in the rationals. The removed sum is ell M_N(C prime), while the retained sum is M_(N ell)(L). Their disjoint partition proves the first-moment formula. Multiplication identifies each coset with K, so there are |K|ell blocks and |K| removed blocks. Thus L has |K|(ell minus one) elements. Setting c equal to one identifies its lift with H. Surjectivity of reduction on units provides d reducing to c, and pi(v) in cK is equivalent to d inverse times v in H, proving L equal to dH. Finally subtract the proven lifted center from the first-moment formula. The small-modulus centers are equal and cancel. No step uses primality of N, oddness of ell, a proper subgroup, an identity coset or cyclicity. Literature priority remains unassessed; no novelty claim is made.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.cosetFinset`
- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.deviation`
- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.liftedFinset`
- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.moment`
- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.reduceUnits`
- Truth anchor: `D5/S3/ArithUnits/MercaCosetFiberLift.result`
