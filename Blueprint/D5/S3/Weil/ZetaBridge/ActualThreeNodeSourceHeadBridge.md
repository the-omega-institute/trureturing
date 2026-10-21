# The literal three-node arithmetic tail Gram

## Abstract

The literal three-node arithmetic tail Gram

The head is the literal signed integer set {-n,0,n}. At each exterior magnitude, the two coordinates are the actual positive and negative arithmetic coupling columns. Their square-summable sequence is an element of a complex Hilbert direct sum at every natural cutoff.

The source map is complex linear. Its Gram quadratic form equals the complete infinite sum of the paired column energy, for arbitrary complex coefficients including zero and cancellation.

The even, odd and second-difference heads have respective normalization factors 1/sqrt(3), 1/sqrt(2) and 1/sqrt(6). For n!=0 their node Gram is the identity, so the sum of squared original retained coefficients equals the Euclidean coefficient mass.

Finite-head zero-energy reconstruction and this original metric imply positive definiteness of the actual three-column Gram at every cutoff. This is a qualitative statement and does not give either branch of sorted spectral asymptotics or a conclusion about RH or Robin.

For every natural c>=3, finite integer head S, natural cutoff N and complex coefficient function v, the complete paired tail energy vanishes exactly when v vanishes on S. The empty head and zero vector are included.

ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower provides the coefficient-uniform lower bound for c>=2: positive C and a cutoff N0 are chosen before all coefficient functions and all later cutoffs. Its summability at N+N0, reindexing of both signed columns and Summable.comp_nat_add give summability at every N.

A retained nonzero coefficient gives strictly positive original coefficient mass. The uniform lower bound gives a positive complete tail at max(N,N0), and nonnegative tail cropping transfers positivity to N. This is a consequence of the uniform estimate; the source realization below uses that consequence on the literal three-node head.

**Theorem 1.1 (actual tail summable all).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_tail_summable_all`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_tail_summable_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) : Summable (pairedColumnTerm c N S v)

**Theorem 1.2 (actual finite head tail pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) : 0 < ∑' j : ℕ, pairedColumnTerm c N S v j

**Theorem 1.3 (actual finite head tail zero iff).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) : (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0

**Definition 1.4 (threeNodes).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

threeNodes(n) is the finite integer set {-n,0,n}. When n is nonzero, these are three distinct nodes.

**Definition 1.5 (pairSpace).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The paired space is EuclideanSpace Complex (Fin 2), with the Hermitian norm on the two exterior signs.

**Definition 1.6 (tailSpace).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail space is lp (fun _ : Nat => pairSpace) 2, the complex Hilbert sum of the paired spaces over all natural sample indices.

**Definition 1.7 (pairedColumnVector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairedColumnVector (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) : pairSpace

**Definition 1.8 (pairedColumnLp).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairedColumnLp {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) (v : ℤ → ℂ) : tailSpace

**Definition 1.9 (sourceColumnMap).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def sourceColumnMap {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : (ℤ → ℂ) →ₗ[ℂ] tailSpace

**Definition 1.10 (singletonHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singletonHead(k) is the complex coefficient function equal to one at k and zero elsewhere.

**Definition 1.11 (headE).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headE(n) is (single(-n)+single(0)+single(n))/sqrt(3).

**Definition 1.12 (headO).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headO(n) is (-single(-n)+single(n))/sqrt(2).

**Definition 1.13 (headS).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headS(n) is (single(-n)-2*single(0)+single(n))/sqrt(6).

**Definition 1.14 (normalizedHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedHead(n) lists headE(n), headO(n) and headS(n) in that order.

**Definition 1.15 (sourceHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceHead(n,x) is the finite sum over i in Fin 3 of x(i) times normalizedHead(n,i).

**Definition 1.16 (sourceTailFamily).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def sourceTailFamily {c : ℕ} (hc : 3 ≤ c) (N : ℕ) (n : ℤ) : Fin 3 → tailSpace

**Theorem 1.17 (source linear combination).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem source_linear_combination {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) (x : Fin 3 → ℂ) : ∑ i, x i • sourceTailFamily hc N n i = sourceColumnMap hc n N (sourceHead n x)

**Theorem 1.18 (actual source gram tsum).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every c>=3, integer n, natural cutoff N and x : Fin 3 -> Complex, let G=Matrix.gram Complex (sourceTailFamily hc N n). Then star(x) dot (G mulVec x) equals the complex cast of the complete sum over j : Nat of pairedColumnTerm c N (threeNodes n) (sourceHead n x) j. No finite truncation is made.

**Definition 1.19 (nodeVector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nodeVector(n,v) is the Euclidean vector [v(-n),v(0),v(n)] in the original signed node order.

**Definition 1.20 (coefficientInner).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coefficientInner(n,v,w) is the Hermitian inner product of nodeVector(n,v) and nodeVector(n,w), conjugate linear in v.

**Definition 1.21 (coefficientGram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coefficientGram(n,b) has entry coefficientInner(n,b(i),b(j)) in row i and column j.

**Theorem 1.22 (normalizedHead coefficient gram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem normalizedHead_coefficient_gram {n : ℤ} (hn : n ≠ 0) : coefficientGram n (normalizedHead n) = 1

**Theorem 1.23 (sourceHead original norm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma sourceHead_original_norm {n : ℤ} (hn : n ≠ 0) (x : Fin 3 → ℂ) : (∑ k ∈ threeNodes n, ‖sourceHead n x k‖ ^ 2) = ∑ i : Fin 3, ‖x i‖ ^ 2

**Theorem 1.24 (actual gram posDef).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_gram_posDef {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) (N : ℕ) : (Matrix.gram ℂ (sourceTailFamily hc N n)).PosDef

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_tail_summable_all`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure](ActualNodalTailEnclosure.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail](ActualUniformFiniteHeadTail.md)
