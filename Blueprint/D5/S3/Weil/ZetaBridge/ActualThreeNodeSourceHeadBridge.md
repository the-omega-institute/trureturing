# The literal three-node arithmetic tail Gram

## Abstract

The literal three-node arithmetic tail Gram

Write g=pi/4, mu=mean(c), a=arithmeticBoundarySymbol(c,n), r=n/N and h=g^2+mu. U,T,C,O are the exact physical finite-form coefficients; their polynomial identities hold for arbitrary real g,mu,a,r.

The even block has diagonal U/3,C/6 and off-diagonal T/sqrt(18). Its trace is 6h+4gar+4(a^2-h)r^2/3+2hr^4/5. Its determinant is the displayed exact polynomial of degrees two through six, with no root-distinctness assumption.

At a=0 the determinant is exactly 32h^2 r^4/45 and the trace is 6h-4hr^2/3+2hr^4/5. The different vanishing order is retained in the exceptional spectral branch.

**Definition 1.1 (U).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.U`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def U (g mu a r : ℝ) : ℝ :=   18 * (g ^ 2 + mu) + 12 * g * a * r +     (8 * a ^ 2 / 3 - 4 * (g ^ 2 + mu)) * r ^ 2 -     2 * g * a * r ^ 3 + 2 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.2 (T).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.T`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def T (g mu a r : ℝ) : ℝ :=   6 * g * a * r + (8 * a ^ 2 / 3 + 4 * (g ^ 2 + mu)) * r ^ 2 +     g * a * r ^ 3 - 4 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.3 (C).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.C`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def C (g mu a r : ℝ) : ℝ :=   8 * a ^ 2 * r ^ 2 / 3 + 4 * g * a * r ^ 3 +     8 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.4 (O).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.O`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.O` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def O (g mu a r : ℝ) : ℝ :=   4 * a ^ 2 + 4 * g * a * r + 4 * (g ^ 2 + mu) * r ^ 2 / 3

**Definition 1.5 (evenDet).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.evenDet`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.evenDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def evenDet (g mu a r : ℝ) : ℝ :=   U g mu a r / 3 * (C g mu a r / 6) -     (T g mu a r / Real.sqrt 18) ^ 2

**Theorem 1.6 (finite trace identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_trace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_trace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_trace_identity (g mu a r : ℝ) :     U g mu a r / 3 + C g mu a r / 6 =       6 * (g ^ 2 + mu) + 4 * g * a * r +         4 / 3 * (a ^ 2 - (g ^ 2 + mu)) * r ^ 2 +         2 * (g ^ 2 + mu) * r ^ 4 / 5

**Theorem 1.7 (finite determinant identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_determinant_identity (g mu a r : ℝ) :     evenDet g mu a r =       (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3) * r ^ 2 +       (4 * g * a * (g ^ 2 + mu) / 3) * r ^ 3 +       (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +         32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 4 +       (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 5 +       (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 6

**Theorem 1.8 (exceptional trace identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_trace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_trace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exceptional_trace_identity (g mu r : ℝ) :     U g mu 0 r / 3 + C g mu 0 r / 6 =       6 * (g ^ 2 + mu) - 4 * (g ^ 2 + mu) * r ^ 2 / 3 +         2 * (g ^ 2 + mu) * r ^ 4 / 5

**Theorem 1.9 (exceptional determinant identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exceptional_determinant_identity (g mu r : ℝ) :     evenDet g mu 0 r = 32 * (g ^ 2 + mu) ^ 2 * r ^ 4 / 45

The head is the literal signed integer set {-n,0,n}. At each exterior magnitude, the two coordinates are the actual positive and negative arithmetic coupling columns. Their square-summable sequence is an element of a complex Hilbert direct sum at every natural cutoff.

The source map is complex linear. Its Gram quadratic form equals the complete infinite sum of the paired column energy, for arbitrary complex coefficients including zero and cancellation.

The even, odd and second-difference heads have respective normalization factors 1/sqrt(3), 1/sqrt(2) and 1/sqrt(6). For n!=0 their node Gram is the identity, so the sum of squared original retained coefficients equals the Euclidean coefficient mass.

Finite-head zero-energy reconstruction and this original metric imply positive definiteness of the actual three-column Gram at every cutoff. For exterior cutoffs the sharp two-sign denominator comparison also controls the finite physical energy.

**Definition 1.10 (threeNodes).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

threeNodes(n) is the finite integer set {-n,0,n}. When n is nonzero, these are three distinct nodes.

**Definition 1.11 (pairSpace).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The paired space is EuclideanSpace Complex (Fin 2), with the Hermitian norm on the two exterior signs.

**Definition 1.12 (tailSpace).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tail space is lp (fun _ : Nat => pairSpace) 2, the complex Hilbert sum of the paired spaces over all natural sample indices.

**Definition 1.13 (pairedColumnVector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairedColumnVector (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) : pairSpace

**Definition 1.14 (pairedColumnLp).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairedColumnLp {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) (v : ℤ → ℂ) : tailSpace

**Definition 1.15 (sourceColumnMap).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def sourceColumnMap {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : (ℤ → ℂ) →ₗ[ℂ] tailSpace

**Definition 1.16 (singletonHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singletonHead(k) is the complex coefficient function equal to one at k and zero elsewhere.

**Definition 1.17 (headE).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headE(n) is (single(-n)+single(0)+single(n))/sqrt(3).

**Definition 1.18 (headO).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headO(n) is (-single(-n)+single(n))/sqrt(2).

**Definition 1.19 (headS).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

headS(n) is (single(-n)-2*single(0)+single(n))/sqrt(6).

**Definition 1.20 (normalizedHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedHead(n) lists headE(n), headO(n) and headS(n) in that order.

**Definition 1.21 (sourceHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceHead(n,x) is the finite sum over i in Fin 3 of x(i) times normalizedHead(n,i).

**Definition 1.22 (sourceTailFamily).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def sourceTailFamily {c : ℕ} (hc : 3 ≤ c) (N : ℕ) (n : ℤ) : Fin 3 → tailSpace

**Theorem 1.23 (source linear combination).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem source_linear_combination {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) (x : Fin 3 → ℂ) : ∑ i, x i • sourceTailFamily hc N n i = sourceColumnMap hc n N (sourceHead n x)

**Theorem 1.24 (actual source gram tsum).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every c>=3, integer n, natural cutoff N and x : Fin 3 -> Complex, let G=Matrix.gram Complex (sourceTailFamily hc N n). Then star(x) dot (G mulVec x) equals the complex cast of the complete sum over j : Nat of pairedColumnTerm c N (threeNodes n) (sourceHead n x) j. No finite truncation is made.

**Definition 1.25 (nodeVector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nodeVector(n,v) is the Euclidean vector [v(-n),v(0),v(n)] in the original signed node order.

**Definition 1.26 (coefficientInner).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coefficientInner(n,v,w) is the Hermitian inner product of nodeVector(n,v) and nodeVector(n,w), conjugate linear in v.

**Definition 1.27 (coefficientGram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coefficientGram(n,b) has entry coefficientInner(n,b(i),b(j)) in row i and column j.

**Theorem 1.28 (normalizedHead coefficient gram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem normalizedHead_coefficient_gram {n : ℤ} (hn : n ≠ 0) : coefficientGram n (normalizedHead n) = 1

**Theorem 1.29 (sourceHead original norm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma sourceHead_original_norm {n : ℤ} (hn : n ≠ 0) (x : Fin 3 → ℂ) : (∑ k ∈ threeNodes n, ‖sourceHead n x k‖ ^ 2) = ∑ i : Fin 3, ‖x i‖ ^ 2

**Theorem 1.30 (actual gram posDef).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_gram_posDef {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) (N : ℕ) : (Matrix.gram ℂ (sourceTailFamily hc N n)).PosDef

**Theorem 1.31 (Strict finite physical energy).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=3, signed n!=0, N>=9 and |n|<N, the finite physical energy is strictly positive for every nonzero complex coefficient vector in the original normalized node basis. The complete source Gram gives positive actual tail energy; its sharp full336 upper bound transfers that strict positivity to the finite form, without an arithmetic nonvanishing premise.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.C`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.O`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.T`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.U`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.evenDet`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_trace_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_trace_identity`
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
- Dependency: [D5/S3/Weil/ZetaBridge/ActualExplicit336](ActualExplicit336.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalCoercivity](ActualNodalCoercivity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure](ActualNodalTailEnclosure.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualPairedReciprocal](ActualPairedReciprocal.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail](ActualUniformFiniteHeadTail.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolResonance](PrimeSymbolResonance.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram](WeilArithmeticCouplingParityGram.md)
