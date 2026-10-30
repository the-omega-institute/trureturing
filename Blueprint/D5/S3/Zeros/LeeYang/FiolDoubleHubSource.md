# Double-hub source

## Abstract

The physical double-hub family: source.

Let m be a natural number at least one. The vertices are a centre, two hubs and m leaves at each hub. Each edge receives an integer total and a positive complementary split. The source endpoint receives k and the other endpoint receives n-k. The mass at a vertex is the sum of its assigned endpoints.

The weight is the product of binomial edge factors and factorial vertex factors over every vertex. At tau=-1 the spin sum equals the product of 1+(-1)^degree X^mass. Formal generators are indexed independently by r. Extracting Z_5 squared times Z_3 to the power 2m selects exactly two edges with total 3; every other edge has total 2. Every cutoff at least 3 gives the same extracted coefficient.

The all-vertex specialization is the expression labelled planarf2, equation (2.19), in Fiol, Martinez-Montoya and Rios Fukelman, arXiv:2006.06379v2. The printed product limit in (2.31) is a separate expression. No claim about an intended correction is needed.

Put H_r=1+X^r and S_r=sum of X^j for 0<=j<r. For odd d, use U=S_d,V=S_(d+1),W=S_(d+2),h=2d,N=d+1. For even d use U=H_d,V=H_(d+1),W=H_(d+2),h=2d-2,N=d+2. The independently defined polynomial is R_m=(1-X)^h Q_(m+1).

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (Edge).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Edge`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines Edge for the physical double-hub family.

**Definition 1.2 (Vertex).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Vertex`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines Vertex for the physical double-hub family.

**Definition 1.3 (src).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.src`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.src` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines src for the physical double-hub family.

**Definition 1.4 (tgt).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.tgt`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.tgt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines tgt for the physical double-hub family.

**Definition 1.5 (graph).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.graph`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines graph for the physical double-hub family.

**Definition 1.6 (automorphismOrder).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.automorphismOrder`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.automorphismOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines automorphismOrder for the physical double-hub family.

**Definition 1.7 (degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.degree`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.degree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines degree for the physical double-hub family.

**Definition 1.8 (mass).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.mass`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines mass for the physical double-hub family.

**Definition 1.9 (J).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.J`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines J for the physical double-hub family.

**Definition 1.10 (vertexWeight).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.vertexWeight`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.vertexWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines vertexWeight for the physical double-hub family.

**Definition 1.11 (edgeBinom).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.edgeBinom`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.edgeBinom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines edgeBinom for the physical double-hub family.

**Definition 1.12 (physicalWeight).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.physicalWeight`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.physicalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines physicalWeight for the physical double-hub family.

**Definition 1.13 (splitSource).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.splitSource`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.splitSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines splitSource for the physical double-hub family.

**Definition 1.14 (allVertexSource).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allVertexSource`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allVertexSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines allVertexSource for the physical double-hub family.

**Definition 1.15 (allSpinSource).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allSpinSource`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allSpinSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines allSpinSource for the physical double-hub family.

**Definition 1.16 (sourcePrefactor).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourcePrefactor`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourcePrefactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines sourcePrefactor for the physical double-hub family.

**Definition 1.17 (sourceTruncation).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceTruncation`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines sourceTruncation for the physical double-hub family.

**Definition 1.18 (targetMonomial).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.targetMonomial`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.targetMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines targetMonomial for the physical double-hub family.

**Definition 1.19 (sourceCoefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceCoefficient`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines sourceCoefficient for the physical double-hub family.

**Definition 1.20 (H).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.H`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines H for the physical double-hub family.

**Definition 1.21 (S).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.S`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines S for the physical double-hub family.

**Definition 1.22 (U).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.U`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines U for the physical double-hub family.

**Definition 1.23 (V).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.V`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines V for the physical double-hub family.

**Definition 1.24 (W).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.W`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines W for the physical double-hub family.

**Definition 1.25 (h).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.h`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines h for the physical double-hub family.

**Definition 1.26 (N).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.N`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines N for the physical double-hub family.

**Definition 1.27 (Q).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Q`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines Q for the physical double-hub family.

**Definition 1.28 (R).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.R`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines R for the physical double-hub family.

**Definition 1.29 (homogeneousSplitSource).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousSplitSource`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousSplitSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines homogeneousSplitSource for the physical double-hub family.

**Definition 1.30 (homogeneousTruncation).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousTruncation`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines homogeneousTruncation for the physical double-hub family.

**Definition 1.31 (homogeneousCoefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousCoefficient`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines homogeneousCoefficient for the physical double-hub family.

**Definition 1.32 (expectedHomogeneousCoefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.expectedHomogeneousCoefficient`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.expectedHomogeneousCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines expectedHomogeneousCoefficient for the physical double-hub family.

**Theorem 1.33 (coefficient extract).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.coefficient_extract`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.coefficient_extract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic extraction uses that new support classification, then evaluates the finite generating sum. Exact source statement: theorem coefficient_extract {E : Type} [Fintype E] [DecidableEq E]     {R : Type} [CommSemiring R] (m cutoff : ℕ)     (hE : Fintype.card E = 2*m+2) (a : (E → ℕ) → R) :     ((∑ n ∈ Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff),       MvPolynomial.C (a n) * ∏ e : E, MvPolynomial.X (2*n e-1) :       MvPolynomial ℕ R).coeff         (Finsupp.single 5 2 + Finsupp.single 3 (2*m))) =     ∑ n ∈ (Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff)).filter       (fun n => (∀ e : E, n e = 2 ∨ n e = 3) ∧         (Finset.univ.filter (fun e : E => n e = 3)).card = 2), a n.

**Theorem 1.34 (pair sum).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.pair_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.pair_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs the bijection between admissible label assignments and two-element edge subsets. Exact source statement: theorem pair_sum {E : Type} [Fintype E] [DecidableEq E]     {R : Type} [AddCommMonoid R] (cutoff : ℕ) (hc : 3 ≤ cutoff)     (a : (E → ℕ) → R) :     (∑ n ∈ (Fintype.piFinset (fun _ : E => Finset.Icc 2 cutoff)).filter       (fun n => (∀ e : E, n e = 2 ∨ n e = 3) ∧         (Finset.univ.filter (fun e : E => n e = 3)).card = 2), a n) =     ∑ A ∈ (Finset.univ : Finset E).powersetCard 2,       a (fun e => if e ∈ A then 3 else 2).

**Theorem 1.35 (source pair formula).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.source_pair_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.source_pair_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem source_pair_formula (m cutoff : ℕ) (hc : 3 ≤ cutoff) :     sourceCoefficient m cutoff =       ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,         Polynomial.C (sourcePrefactor (fun e => if e ∈ A then 3 else 2)) *           allVertexSource (fun e => if e ∈ A then 3 else 2).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Edge`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.H`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.J`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.N`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Q`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.R`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.S`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.U`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.V`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.Vertex`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.W`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allSpinSource`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.allVertexSource`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.automorphismOrder`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.coefficient_extract`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.edgeBinom`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.expectedHomogeneousCoefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.graph`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.h`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousCoefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousSplitSource`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.homogeneousTruncation`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.mass`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.pair_sum`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.physicalWeight`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceCoefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourcePrefactor`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.sourceTruncation`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.source_pair_formula`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.splitSource`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.src`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.targetMonomial`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.tgt`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubSource.vertexWeight`
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
