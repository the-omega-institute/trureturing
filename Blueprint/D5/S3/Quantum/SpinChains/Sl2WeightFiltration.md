# Weight filtration and maximal power ranks

## Abstract

Integral sl₂ weights give sharp rank bounds for endomorphisms lowering the weight filtration.

Let K be a field of characteristic zero and V a finite-dimensional K-vector space. The relations ef − fe = h, he − eh = 2e and hf − fh = −2f include the zero action. The space weightSpace(h,s) is the eigenspace of h at the scalar obtained from the integer s. IntegralWeights(h) means that a finite collection of integer weight spaces spans V. The spaces weightLE(h,s) and weightGE(h,s) are the sums of weights at most s and at least s, respectively. Operator powers use composition; finrank denotes dimension over K.

**Theorem 1.1 (Raising shifts weights).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall v \in V,\; (v \in \operatorname{weightSpace}\left(h, s\right)) \Rightarrow (\forall r \in \mathbb{N},\; (e^{r})\left(v\right) \in \operatorname{weightSpace}\left(h, s + 2 \cdot (r : \mathbb{Z})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_pow_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator of h with e implies that the rth raising power increases weight by twice r.

**Theorem 1.2 (Lowering shifts weights).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall v \in V,\; (v \in \operatorname{weightSpace}\left(h, s\right)) \Rightarrow (\forall r \in \mathbb{N},\; (f^{r})\left(v\right) \in \operatorname{weightSpace}\left(h, s - 2 \cdot (r : \mathbb{Z})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator of h with f implies that the rth lowering power decreases weight by twice r.

**Theorem 1.3 (Local raising nilpotence).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall v \in V,\; (v \in \operatorname{weightSpace}\left(h, s\right)) \Rightarrow (\exists n \in \mathbb{N},\; (e^{n})\left(v\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_locally_nilpotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonzero successive raising iterates have distinct eigenvalues. An infinite sequence of such vectors would be linearly independent, contradicting finite dimensionality.

**Theorem 1.4 (Local lowering nilpotence).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall v \in V,\; (v \in \operatorname{weightSpace}\left(h, s\right)) \Rightarrow (\exists n \in \mathbb{N},\; (f^{n})\left(v\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_locally_nilpotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successive lowering iterates likewise have distinct weights, so every weight vector is eventually annihilated.

**Theorem 1.5 (Injectivity above the exponent).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall r \in \mathbb{N},\; ((r : \mathbb{Z}) \le s) \Rightarrow (\forall x \in \operatorname{weightSpace}\left(h, s\right),\; \forall y \in \operatorname{weightSpace}\left(h, s\right),\; ((f^{r})\left(x\right) = (f^{r})\left(y\right)) \Rightarrow (x = y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lowering power is injective on weights at least its exponent. Local raising nilpotence supplies the kernel criterion, including the zero representation.

**Theorem 1.6 (Injectivity below the negative exponent).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall r \in \mathbb{N},\; (s \le -(r : \mathbb{Z})) \Rightarrow (\forall x \in \operatorname{weightSpace}\left(h, s\right),\; \forall y \in \operatorname{weightSpace}\left(h, s\right),\; ((e^{r})\left(x\right) = (e^{r})\left(y\right)) \Rightarrow (x = y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_pow_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interchanging e and f and replacing h by its negative gives injectivity of raising powers on sufficiently negative weights.

**Theorem 1.7 (Symmetry of weight dimensions).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \operatorname{finrank}\left(K, \operatorname{weightSpace}\left(h, s\right)\right) = \operatorname{finrank}\left(K, \operatorname{weightSpace}\left(h, -s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.weight_finrank_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injections in both directions between opposite weight spaces force their dimensions to agree.

**Theorem 1.8 (Surjectivity onto negative weights).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow (\forall t \in \mathbb{Z},\; \forall r \in \mathbb{N},\; (t \le -(r : \mathbb{Z})) \Rightarrow (\forall y \in V,\; (y \in \operatorname{weightSpace}\left(h, t\right)) \Rightarrow (\exists x \in V,\; (x \in \operatorname{weightSpace}\left(h, t + 2 \cdot (r : \mathbb{Z})\right)) \land ((f^{r})\left(x\right) = y))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lowering from the opposite positive weight is bijective. Factoring this power gives a preimage for every smaller lowering power with sufficiently negative target.

**Theorem 1.9 (Exact rank of a lowering power).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow ((\operatorname{IntegralWeights}\left(h\right)) \Rightarrow (\forall r \in \mathbb{N},\; \operatorname{finrank}\left(K, \operatorname{range}\left(f^{r}\right)\right) = \operatorname{finrank}\left(K, \operatorname{weightGE}\left(h, (r : \mathbb{Z})\right)\right) + \operatorname{finrank}\left(K, \operatorname{weightLE}\left(h, -(r : \mathbb{Z}) - 1\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_rank_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the representation at weight r. The lowering power is injective on the upper part and maps the lower part onto weights at most minus r minus one. The two image subspaces are disjoint.

**Theorem 1.10 (Iterated filtration decrease).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall F \in \mathbb{Z} \to \operatorname{Submodule}\left(K, V\right),\; \forall T \in \operatorname{End}\left(K, V\right),\; (\forall s \in \mathbb{Z},\; \operatorname{map}\left(F\left(s\right), T\right) \le F\left(s - 2\right)) \Rightarrow (\forall s \in \mathbb{Z},\; \forall r \in \mathbb{N},\; \operatorname{map}\left(F\left(s\right), T^{r}\right) \le F\left(s - 2 \cdot (r : \mathbb{Z})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.filtration_pow_map_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the exponent adds the two-unit filtration decrease at each application. No exhaustiveness or boundedness assumption on the filtration is required.

**Theorem 1.11 (Maximal power ranks).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall h \in \operatorname{End}\left(K, V\right),\; \forall e \in \operatorname{End}\left(K, V\right),\; \forall f \in \operatorname{End}\left(K, V\right),\; (\operatorname{Sl2Relations}\left(h, e, f\right)) \Rightarrow ((\operatorname{IntegralWeights}\left(h\right)) \Rightarrow (\forall T \in \operatorname{End}\left(K, V\right),\; (\forall s \in \mathbb{Z},\; \operatorname{map}\left(\operatorname{weightLE}\left(h, s\right), T\right) \le \operatorname{weightLE}\left(h, s - 2\right)) \Rightarrow (\forall r \in \mathbb{N},\; \operatorname{finrank}\left(K, \operatorname{range}\left(T^{r}\right)\right) \le \operatorname{finrank}\left(K, \operatorname{range}\left(f^{r}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.rank_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict a power of T from weights at most r minus one to weights at most minus r minus one. Rank-nullity bounds its kernel from below. The exact lowering rank formula then gives the power-rank comparison for every natural exponent.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.filtration_pow_map_le`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_locally_nilpotent`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_injective`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_surjective`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_pow_weight`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.lowering_rank_formula`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_locally_nilpotent`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_pow_injective`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.raising_pow_weight`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.rank_comparison`
- Truth anchor: `D5/S3/Quantum/SpinChains/Sl2WeightFiltration.weight_finrank_symm`
- Dependency: [D5/S3/Quantum/SpinChains/Sl2WeightInjectivity](Sl2WeightInjectivity.md)
