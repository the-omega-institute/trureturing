# Conical transfer through a halfspace

## Abstract

A conical property on a finitely generated cone intersected with a halfspace follows from positive generators and positive-negative cancellation pairs.

**Theorem 1.1 (Positive-negative mass decomposition).**

$$\forall (I:Type), \forall (E:Type), [Fintype\left(I\right)] [AddCommGroup\left(E\right)] [Module\left(\mathbb{R}, E\right)] \forall (Good:E\to Prop), ((Good\left(0\right))\land ((\forall (u:E), \forall (w:E), ((Good\left(u\right))\land (Good\left(w\right)))\Rightarrow Good\left(u+w\right))\land (\forall (t:\mathbb{R}), \forall (u:E), ((0\leq t)\land (Good\left(u\right)))\Rightarrow Good\left(t\cdot u\right))))\Rightarrow \forall (v:I\to E), \forall (a:I\to \mathbb{R}), \forall (x:I\to \mathbb{R}), ((\forall (j:I), 0\leq x\left(j\right))\land ((0\leq \sum_{j:I} x\left(j\right)\cdot a\left(j\right))\land ((\forall (j:I), (0\leq a\left(j\right))\Rightarrow Good\left(v\left(j\right)\right))\land (\forall (j:I), \forall (k:I), ((0<a\left(j\right))\land (a\left(k\right)<0))\Rightarrow Good\left((-a\left(k\right))\cdot v\left(j\right)+a\left(j\right)\cdot v\left(k\right)\right)))))\Rightarrow Good\left(\sum_{j:I} x\left(j\right)\cdot v\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.halfspace_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Good contain zero and be closed under addition and multiplication by nonnegative real scalars. Let v be a finite family and a assign a real value to each generator. A nonnegative combination whose total a-value is nonnegative satisfies Good if the generators with nonnegative value and all positive-negative cancellation pairs satisfy Good. The proof partitions the generators by the sign of a, matches negative mass with positive mass, and retains the unused positive mass. When positive mass is zero, every negatively valued coefficient vanishes.

SharedSpectral.spectralGood(c,x) means that the Euclidean norm of x is at most c times its coordinate sum. step(d,j) is the vector with value one at k when k.val<j and zero otherwise. synth(p,x) is the sum over j of x(j) times step(d,p(j)). extend(l,a) equals l(a) for a<d and zero otherwise; spectralGap(l,j)=extend(l,j.val)-extend(l,j.val+1). Natural step lengths, minima and values are computed before real coercion. The original two-row proof uses these shared lemmas; the three-row proof also uses the norm, step-synthesis, gap and additive-closure lemmas. The general mixture lemma remains a supplier of the original proof.

**Theorem 1.2 (The zero spectrum satisfies every cone bound).**

$$\forall (d:\mathbb{N}), \forall (c:\mathbb{R}), SharedSpectral.spectralGood\left(c, (0:Fin\left(d\right)\to \mathbb{R})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension may be zero and c may have either sign.

**Theorem 1.3 (Addition preserves a common cone bound).**

$$\forall (d:\mathbb{N}), \forall (c:\mathbb{R}), \forall (x:Fin\left(d\right)\to \mathbb{R}), \forall (y:Fin\left(d\right)\to \mathbb{R}), ((SharedSpectral.spectralGood\left(c, x\right))\land (SharedSpectral.spectralGood\left(c, y\right)))\Rightarrow SharedSpectral.spectralGood\left(c, x+y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both vectors have the same dimension and coefficient c.

**Theorem 1.4 (Nonnegative scaling preserves the cone bound).**

$$\forall (d:\mathbb{N}), \forall (c:\mathbb{R}), \forall (t:\mathbb{R}), \forall (x:Fin\left(d\right)\to \mathbb{R}), ((0\leq t)\land (SharedSpectral.spectralGood\left(c, x\right)))\Rightarrow SharedSpectral.spectralGood\left(c, t\cdot x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale t may vanish; c need not be nonnegative.

**Theorem 1.5 (A squared estimate implies the norm estimate).**

$$\forall (d:\mathbb{N}), \forall (c:\mathbb{R}), \forall (x:Fin\left(d\right)\to \mathbb{R}), (((0\leq c)\land (0\leq \sum_{i:Fin\left(d\right)} x\left(i\right)))\land (\sum_{i:Fin\left(d\right)} (x\left(i\right))^{2}\leq (c)^{2}\cdot (\sum_{i:Fin\left(d\right)} x\left(i\right))^{2}))\Rightarrow SharedSpectral.spectralGood\left(c, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_of_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient and total mass are nonnegative; no entrywise sign condition is imposed here.

**Theorem 1.6 (A norm estimate implies the squared estimate).**

$$\forall (d:\mathbb{N}), \forall (c:\mathbb{R}), \forall (x:Fin\left(d\right)\to \mathbb{R}), (((0\leq c)\land (0\leq \sum_{i:Fin\left(d\right)} x\left(i\right)))\land (SharedSpectral.spectralGood\left(c, x\right)))\Rightarrow \sum_{i:Fin\left(d\right)} (x\left(i\right))^{2}\leq (c)^{2}\cdot (\sum_{i:Fin\left(d\right)} x\left(i\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient and total mass are nonnegative.

**Theorem 1.7 (Mass of a step spectrum).**

$$\forall (d:\mathbb{N}), \forall (j:\mathbb{N}), (j\leq d)\Rightarrow \sum_{k:Fin\left(d\right)} SharedSpectral.step\left(d, j, k\right)=(j:\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural step length j lies between zero and d.

**Theorem 1.8 (Gram kernel of two step spectra).**

$$\forall (d:\mathbb{N}), \forall (i:\mathbb{N}), \forall (j:\mathbb{N}), ((i\leq d)\land (j\leq d))\Rightarrow \sum_{k:Fin\left(d\right)} SharedSpectral.step\left(d, i, k\right)\cdot SharedSpectral.step\left(d, j, k\right)=(min\left(i, j\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_step_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlap is their natural minimum, coerced to the reals.

**Theorem 1.9 (Mass of a synthesized spectrum).**

$$\forall (d:\mathbb{N}), \forall (m:\mathbb{N}), \forall (p:Fin\left(m\right)\to \mathbb{N}), \forall (x:Fin\left(m\right)\to \mathbb{R}), (\forall (j:Fin\left(m\right)), p\left(j\right)\leq d)\Rightarrow \sum_{k:Fin\left(d\right)} SharedSpectral.synth\left(p, x, k\right)=\sum_{j:Fin\left(m\right)} x\left(j\right)\cdot (p\left(j\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.mass_synth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite list p consists of step lengths at most d. Coefficients x are arbitrary real numbers.

**Theorem 1.10 (Gram expansion of a synthesized spectrum).**

$$\forall (d:\mathbb{N}), \forall (m:\mathbb{N}), \forall (p:Fin\left(m\right)\to \mathbb{N}), \forall (x:Fin\left(m\right)\to \mathbb{R}), (\forall (j:Fin\left(m\right)), p\left(j\right)\leq d)\Rightarrow \sum_{k:Fin\left(d\right)} (SharedSpectral.synth\left(p, x, k\right))^{2}=\sum_{i:Fin\left(m\right)} \sum_{j:Fin\left(m\right)} x\left(i\right)\cdot x\left(j\right)\cdot (min\left(p\left(i\right), p\left(j\right)\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.square_synth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All d,m and real coefficient vectors are allowed, subject only to p(j) at most d.

**Theorem 1.11 (Ordered nonnegative spectra have nonnegative gaps).**

$$\forall (d:\mathbb{N}), \forall (l:Fin\left(d\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (j:Fin\left(d\right)), 0\leq l\left(j\right)))\Rightarrow \forall (j:Fin\left(d\right)), 0\leq SharedSpectral.spectralGap\left(l, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGap_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The last gap uses the extension by zero.

**Theorem 1.12 (Adjacent differences telescope on any natural interval).**

$$\forall (d:\mathbb{N}), \forall (l:Fin\left(d\right)\to \mathbb{R}), \forall (a:\mathbb{N}), \forall (b:\mathbb{N}), (a\leq b)\Rightarrow \sum_{j\in Ico\left(a, b\right)} (SharedSpectral.extend\left(l, j\right)-SharedSpectral.extend\left(l, j+1\right))=SharedSpectral.extend\left(l, a\right)-SharedSpectral.extend\left(l, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.gap_telescope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval is Ico(a,b); b need not be at most d because the extension is zero beyond d.

**Theorem 1.13 (All adjacent gaps reconstruct the spectrum).**

$$\forall (d:\mathbb{N}), \forall (l:Fin\left(d\right)\to \mathbb{R}), \sum_{j:Fin\left(d\right)} SharedSpectral.spectralGap\left(l, j\right)\cdot SharedSpectral.step\left(d, val\left(j\right)+1\right)=l$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.gap_reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds for every real spectrum, with no ordering or sign hypothesis.

**Theorem 1.14 (Finite sums preserve an additive predicate).**

$$\forall (I:Type), \forall (E:Type), (AddCommMonoid\left(E\right))\Rightarrow \forall (Good:E\to Prop), ((Good\left(0\right))\land (\forall (u:E), \forall (v:E), ((Good\left(u\right))\land (Good\left(v\right)))\Rightarrow Good\left(u+v\right)))\Rightarrow \forall (s:Finset\left(I\right)), \forall (f:I\to E), (\forall (i:I), (i\in s)\Rightarrow Good\left(f\left(i\right)\right))\Rightarrow Good\left(\sum_{i\in s} f\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_mem_of_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I and E are arbitrary types; E is an additive commutative monoid. The finite set s may be empty. Good contains zero and is closed under addition.

**Theorem 1.15 (A fixed-base cone bound survives mixing).**

$$\forall (I:Type), \forall (E:Type), ((AddCommGroup\left(E\right))\land (Module\left(\mathbb{R}, E\right)))\Rightarrow \forall (Good:E\to Prop), (((Good\left(0\right))\land (\forall (u:E), \forall (v:E), ((Good\left(u\right))\land (Good\left(v\right)))\Rightarrow Good\left(u+v\right)))\land (\forall (t:\mathbb{R}), \forall (u:E), ((0\leq t)\land (Good\left(u\right)))\Rightarrow Good\left(t\cdot u\right)))\Rightarrow \forall (s:Finset\left(I\right)), \forall (x:I\to \mathbb{R}), \forall (v:I\to E), \forall (b:E), ((Nonempty\left(s\right))\land (\forall (i:I), (i\in s)\Rightarrow 0\leq x\left(i\right))\land (\forall (i:I), (i\in s)\Rightarrow Good\left(b+\sum_{j\in s} x\left(j\right)\cdot v\left(i\right)\right)))\Rightarrow Good\left(b+\sum_{i\in s} x\left(i\right)\cdot v\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.mixture_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I and E are arbitrary types; E is an additive commutative group and real module. Good contains zero and is closed under addition and nonnegative real scaling. The finite set s is nonempty; all weights on s are nonnegative. Writing M for their sum, the premises are Good(b+M*v(i)) at every i in s. The proof treats M=0 without division and M>0 by barycentric weights.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.gap_reconstruct`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.gap_telescope`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.halfspace_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.mass_synth`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.mixture_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGap_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_add`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_of_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_smul`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.spectralGood_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.square_synth`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_mem_of_closed`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_step`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.sum_step_mul`
