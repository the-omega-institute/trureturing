# Conical transfer through a halfspace

## Abstract

A conical property on a finitely generated cone intersected with a halfspace follows from positive generators and positive-negative cancellation pairs.

**Theorem 1.1 (Positive-negative mass decomposition).**

$$\forall (I:Type), \forall (E:Type), [Fintype\left(I\right)] [AddCommGroup\left(E\right)] [Module\left(\mathbb{R}, E\right)] \forall (Good:E\to Prop), ((Good\left(0\right))\land ((\forall (u:E), \forall (w:E), ((Good\left(u\right))\land (Good\left(w\right)))\Rightarrow Good\left(u+w\right))\land (\forall (t:\mathbb{R}), \forall (u:E), ((0\leq t)\land (Good\left(u\right)))\Rightarrow Good\left(t\cdot u\right))))\Rightarrow \forall (v:I\to E), \forall (a:I\to \mathbb{R}), \forall (x:I\to \mathbb{R}), ((\forall (j:I), 0\leq x\left(j\right))\land ((0\leq \sum_{j:I} x\left(j\right)\cdot a\left(j\right))\land ((\forall (j:I), (0\leq a\left(j\right))\Rightarrow Good\left(v\left(j\right)\right))\land (\forall (j:I), \forall (k:I), ((0<a\left(j\right))\land (a\left(k\right)<0))\Rightarrow Good\left((-a\left(k\right))\cdot v\left(j\right)+a\left(j\right)\cdot v\left(k\right)\right)))))\Rightarrow Good\left(\sum_{j:I} x\left(j\right)\cdot v\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.halfspace_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Good contain zero and be closed under addition and multiplication by nonnegative real scalars. Let v be a finite family and a assign a real value to each generator. A nonnegative combination whose total a-value is nonnegative satisfies Good if the generators with nonnegative value and all positive-negative cancellation pairs satisfy Good. The proof partitions the generators by the sign of a, matches negative mass with positive mass, and retains the unused positive mass. When positive mass is zero, every negatively valued coefficient vanishes.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.halfspace_transfer`
