# Nearest affine independent-bit laws on four points

## Abstract

An exact total variation projection onto affine independent-bit laws on four points.

**Theorem 1.1 (The exact distance is attained with three independent bits).**

$$\begin{aligned}\forall p:\operatorname{Fin}(4)\to \mathbb{R},(\forall j:\operatorname{Fin}(4),0\le \operatorname{p}(j)) \land \sum_{j} \operatorname{p}(j)=1 \longrightarrow \\(\forall I [\operatorname{Fintype}(I)],s:A,c:I\to A,t:I\to \mathbb{R},(\forall j:I,\operatorname{t}(j) \in [0,1]) \longrightarrow \operatorname{d}(p)\le \operatorname{TV}(p,\operatorname{L}(s,c,t))) \land \\(\exists s:A,c:\operatorname{Fin}(3)\to A,t:\operatorname{Fin}(3)\to \mathbb{R},(\forall j:\operatorname{Fin}(3),\operatorname{t}(j) \in [0,1]) \land \operatorname{TV}(p,\operatorname{L}(s,c,t))=\operatorname{d}(p))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FourPointAffineProjection.affine_projection_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output space A is the product of two copies of the binary field. The law L is the affine sum of independent bits. Its arguments are the offset s, the column map c, and the Bernoulli rates t. The four masses are read at 00, 10, 01, 11 in that order.

The rate bounds make each Bernoulli factor a nonnegative unit-mass law, and the finite index set supplies a finite product of these factors. Both probability assumptions on p are needed. Direct arithmetic gives d(p) = 0 for the zero mass function, which has distance one-half from every comparison law. For signed masses (1, -1, 0, 1) of total mass one, the formula gives one-half. The negative atom alone forces distance at least one to every probability law because the total masses agree.

To evaluate d(p), relabel the atoms by placing their masses in the order largest, smallest, second-smallest, second-largest. The first coordinate and the sum of the coordinates then have moments a and h with 0 <= a <= h. Their product character has signed moment b with |b| <= a.

$\operatorname{d}(p)=\frac{\max (0,ah-b)}{2(1+h)}$

Each atom changes by at most the total variation. Together with the multiplicative and sign inequalities on the moments, this limits how far a competitor can reduce the violated moment constraint. If the constraint is violated, transferring mass between two atoms while preserving h attains the bound with a product law. Otherwise, three bias factors realize the original moments. An affine inverse relabeling preserves the class of laws and the total variation.

## References

- Truth anchor: `D5/S3/TotalVariation/FourPointAffineProjection.affine_projection_exact`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
