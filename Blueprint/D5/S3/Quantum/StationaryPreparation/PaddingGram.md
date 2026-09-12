# The Gram Entries of Padding Residuals

## Abstract

Padding Gram entries are minimum-head multiplicities within each tail block.

Let A be a finite type with decidable equality and let h be a letter of A. For a multiset b, tail(h,b) is the full multiset obtained by filtering out h; count(h,b) is the number of occurrences of h, and tailCount(h,b) is the number of all other letters, counted with multiplicity. The existing headSlice(h,b,j) is replicate(j,h) + tail(h,b). multiplicity(card(q),q) counts words with occupation q. castR and castC are the natural-number inclusions into the real and complex scalars. The subtraction j-1 in a head index is natural subtraction.

**Theorem 1.1 (Consecutive multiplicity increments).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall b \in Multiset\left(A\right),\; 0 < tailCount\left(h, b\right) \Rightarrow \left(\forall j \in \mathbb{N},\; lastTailMass\left(h, headSlice\left(h, b, j\right)\right) = if\left(j = 0, castR\left(multiplicity\left(card\left(headSlice\left(h, b, 0\right)\right), headSlice\left(h, b, 0\right)\right)\right), castR\left(multiplicity\left(card\left(headSlice\left(h, b, j\right)\right), headSlice\left(h, b, j\right)\right)\right) - castR\left(multiplicity\left(card\left(headSlice\left(h, b, j - 1\right)\right), headSlice\left(h, b, j - 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.last_tail_mass_head_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j, the last-tail mass of the j-th head slice is its multiplicity increment. At j=0 it is the initial multiplicity. The sole positivity assumption is tailCount(h,b)>0; no ambient capacity or positive head count is required. lastTailMass(h,q) is tailCount(h,q) times multiplicity(card(q),q), divided by card(q), in the reals. The head-removal multiplicity recurrence gives the difference formula.

For b<=a in multiset order, paddingResidual(h,a,b) is the existing vector in Space(OccupationMemory(a,h)). A zero tail gives the sink basis vector. A positive tail gives the sum, for 0<=j<=count(h,b), of the basis vector at its actual tail and head index j, weighted by the complex inclusion of sqrt(lastTailMass(h,headSlice(h,b,j))). InnerC is the complex inner product, conjugate linear in the first argument and linear in the second.

**Theorem 1.2 (Whole-tail blocks and minimum head count).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; \forall c \in Multiset\left(A\right),\; \left(b \le a \land c \le a\right) \Rightarrow InnerC\left(paddingResidual\left(h, a, b\right), paddingResidual\left(h, a, c\right)\right) = if\left(tail\left(h, b\right) = tail\left(h, c\right), castC\left(multiplicity\left(card\left(headSlice\left(h, b, min\left(count\left(h, b\right), count\left(h, c\right)\right)\right)\right), headSlice\left(h, b, min\left(count\left(h, b\right), count\left(h, c\right)\right)\right)\right)\right), 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_residual_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Different entire tails give inner product zero, even when their cardinalities agree. Equal positive tails share precisely the head indices up to the smaller head count. Orthonormality multiplies their real square-root weights, and the finite sum of multiplicity increments gives the displayed entry. If both tails are zero, both vectors are the sink and the pure-head multiplicity is one. A sink and a positive-tail vector are orthogonal. This includes empty occupations and zero head capacity. No maximal-head or positive-head assumption is present.

residualScale(b) is the existing positive real sqrt(multiplicity(card(b),b)). normalizedPadding(h,a,b) divides the actual padding residual by its complex inclusion. smulC denotes complex scalar multiplication, inv is scalar inverse, castRC is the real-to-complex inclusion, and sink(a,h) is basis(none) in the same Space(OccupationMemory(a,h)). This is the actual terminal padding coordinate: the existing physical memory embedding sends it to physicalFinal(a) for the chosen maximal head. paddingMoment uses this sink in its second operand.

**Definition 1.3 (Actual normalized padding vectors).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; normalizedPadding\left(h, a, b\right) = smulC\left(inv\left(castRC\left(residualScale\left(b\right)\right)\right), paddingResidual\left(h, a, b\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalizedPadding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive real scale fixes one coherent normalization, including phase.

**Definition 1.4 (Actual source moments).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; paddingMoment\left(h, a, b\right) = InnerC\left(normalizedPadding\left(h, a, b\right), sink\left(a, h\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/StationaryPreparation/PaddingGram.paddingMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first argument is conjugated. The common sink is the second argument.

**Theorem 1.5 (Unit residual vectors).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; b \le a \Rightarrow norm\left(normalizedPadding\left(h, a, b\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal Gram entry is M(b); dividing by its positive square root gives norm one.

**Theorem 1.6 (Pure-head vectors share the sink).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; \left(b \le a \land tailCount\left(h, b\right) = 0\right) \Rightarrow normalizedPadding\left(h, a, b\right) = sink\left(a, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_tail_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A legal occupation with zero tail has multiplicity one and its actual vector is the sink.

**Theorem 1.7 (The terminal vector).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; normalizedPadding\left(h, a, 0\right) = sink\left(a, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero occupation always lies in the capacity box. Its normalized vector is the unit terminal sink.

**Theorem 1.8 (Every source moment in its actual domain).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall b \in Multiset\left(A\right),\; b \le a \Rightarrow paddingMoment\left(h, a, b\right) = if\left(tailCount\left(h, b\right) = 0, 1, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ternary if(P,x,y) means x when P holds and y otherwise. Thus z(0)=1; all nonzero moments off the head axis vanish. The positive-tail vector has no sink coordinate.

**Theorem 1.9 (All legal head-axis vectors coincide).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall j \in \mathbb{N},\; j \le count\left(h, a\right) \Rightarrow normalizedPadding\left(h, a, replicate\left(j, h\right)\right) = sink\left(a, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This includes j=0 and every 1<=j<=count(h,a). In particular phi(0)=phi(e_h) when count(h,a)>0; no positive-capacity hypothesis is needed for j=0.

**Theorem 1.10 (Prescribed head-axis moments).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall h \in A,\; \forall a \in Multiset\left(A\right),\; \forall j \in \mathbb{N},\; j \le count\left(h, a\right) \Rightarrow paddingMoment\left(h, a, replicate\left(j, h\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_moment_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All legal pure-head moments are exactly one. The statements hold for any head; choosing a maximal head gives the axis required by the attainment source.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.last_tail_mass_head_slice`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalizedPadding`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_axis`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_norm`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_tail_free`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.normalized_padding_zero`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.paddingMoment`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_moment`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_moment_axis`
- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingGram.padding_residual_inner`
- Dependency: [D5/S3/Quantum/StationaryPreparation/NormalizedGram](NormalizedGram.md)
- Dependency: [D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit](StationaryOccupationResidualCircuit.md)
