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

The exact finite coefficients and their trace and determinant identities are stated with the literal three-node arithmetic source Gram in ActualThreeNodeSourceHeadBridge.

The signed integer nodes are the sealed owner's literal set {-n,0,n}; n is any nonzero integer. The same owner supplies the normalized source heads and sourceHead. No new Hilbert-space bridge, summability theorem or positivity definition is introduced here.

Nodal expansion derives D=X(X^2-n^2), Q=(v(-n)+v(0)+v(n))X^2+n(v(n)-v(-n))X-n^2 v(0), and P=a(v(n)-v(-n))X^2+an(v(n)+v(-n))X from the actual arithmetic symbol and its oddness.

For raw coordinates v=p(1,1,1)+q(-1,0,1)+s(1,-2,1), reciprocal evaluation gives A(t)=2aq+2ar(p+s)t and B(t)=3p+2rq t+r^2(-p+2s)t^2. Both exterior signs are kept before integration. All p,q,s are complex and may vanish or cancel.

The paired energy integral is U|p|^2+2O|q|^2+C|s|^2+2T Re(conj(p)s). Substituting p=x(0)/sqrt(3), q=x(1)/sqrt(2), s=x(2)/sqrt(6) gives the Hermitian matrix [[U/3,0,T/sqrt(18)],[0,O,0],[T/sqrt(18),0,C/6]].

The sealed sourceHead_original_norm theorem identifies the original retained coefficient mass with the Euclidean mass of x. The realized matrix therefore uses that original metric; it is derived from actual P,Q and pairedEnergy, rather than selected as an unrelated Hermitian matrix.

**Theorem 1.32 (nodes distinct).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma nodes_distinct {n : ℤ} (hn : n ≠ 0) :     -n ≠ 0 ∧ -n ≠ n ∧ (0 : ℤ) ≠ n

**Theorem 1.33 (threeNodes card).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma threeNodes_card {n : ℤ} (hn : n ≠ 0) : (threeNodes n).card = 3

**Theorem 1.34 (actual symbol zero).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_symbol_zero (c : ℕ) : arithmeticBoundarySymbol c 0 = 0

**Theorem 1.35 (actual three nodal).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_three_nodal {n : ℤ} (hn : n ≠ 0) (c : ℕ) (v : ℤ → ℂ) :     D (threeNodes n) = X * (X ^ 2 - C ((n : ℂ) ^ 2)) ∧     Q (threeNodes n) v =       C (v (-n) + v 0 + v n) * X ^ 2 +         C ((n : ℂ) * (v n - v (-n))) * X - C ((n : ℂ) ^ 2 * v 0) ∧     P c (threeNodes n) v =       C ((arithmeticBoundarySymbol c n : ℂ) * (v n - v (-n))) * X ^ 2 +         C ((arithmeticBoundarySymbol c n : ℂ) * (n : ℂ) * (v n + v (-n))) * X

**Definition 1.36 (rawHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawHead (n : ℤ) (p q s : ℂ) : ℤ → ℂ :=   p • (singletonHead (-n) + singletonHead 0 + singletonHead n) +   q • (-singletonHead (-n) + singletonHead n) +   s • (singletonHead (-n) - 2 • singletonHead 0 + singletonHead n)

**Theorem 1.37 (rawHead nodes).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawHead_nodes {n : ℤ} (hn : n ≠ 0) (p q s : ℂ) :     rawHead n p q s (-n) = p - q + s ∧     rawHead n p q s 0 = p - 2 * s ∧     rawHead n p q s n = p + q + s

**Theorem 1.38 (sourceHead eq rawHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma sourceHead_eq_rawHead (n : ℤ) (x : Fin 3 → ℂ) :     sourceHead n x = rawHead n (x 0 / (Real.sqrt 3 : ℂ))       (x 1 / (Real.sqrt 2 : ℂ)) (x 2 / (Real.sqrt 6 : ℂ))

**Definition 1.39 (rawA).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawA (a r : ℝ) (p q s : ℂ) : ℂ[X] :=   C (2 * (a : ℂ) * q) + C (2 * (a : ℂ) * (r : ℂ) * (p + s)) * X

**Definition 1.40 (rawB).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawB (r : ℝ) (p q s : ℂ) : ℂ[X] :=   C (3 * p) + C (2 * (r : ℂ) * q) * X +     C ((r : ℂ) ^ 2 * (-p + 2 * s)) * X ^ 2

**Theorem 1.41 (reciprocal three).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma reciprocal_three (N : ℕ) (b0 b1 b2 : ℂ) :     reciprocalPolynomial 3 N (C b0 + C b1 * X + C b2 * X ^ 2) =       C b2 + C (b1 / (N : ℂ)) * X + C (b0 / (N : ℂ) ^ 2) * X ^ 2

**Theorem 1.42 (actual raw reciprocals).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_raw_reciprocals {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (p q s : ℂ) :     reciprocalPolynomial 3 N (P c (threeNodes n) (rawHead n p q s)) =       rawA (arithmeticBoundarySymbol c n) ((n : ℝ) / N) p q s ∧     reciprocalPolynomial 3 N (Q (threeNodes n) (rawHead n p q s)) =       rawB ((n : ℝ) / N) p q s

**Definition 1.43 (mixed).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def mixed (p s : ℂ) : ℝ := (conj p * s).re

**Definition 1.44 (rawIntegrand).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rawIntegrand (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) : ℝ :=   ‖value (rawA a r p q s) t + (g : ℂ) * value (rawB r p q s) t‖ ^ 2 +   ‖value (rawA a r p q s) (-t) - (g : ℂ) * value (rawB r p q s) (-t)‖ ^ 2 +   mu * (‖value (rawB r p q s) t‖ ^ 2 + ‖value (rawB r p q s) (-t)‖ ^ 2)

**Definition 1.45 (quarticCoeffs).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def quarticCoeffs (g mu a r : ℝ) (p q s : ℂ) : Fin 5 → ℝ :=   ![18 * (g ^ 2 + mu) * ‖p‖ ^ 2 + 8 * a ^ 2 * ‖q‖ ^ 2,     24 * g * a * r * (‖p‖ ^ 2 + mixed p s) + 16 * a * g * r * ‖q‖ ^ 2,     (8 * a ^ 2 - 12 * (g ^ 2 + mu)) * r ^ 2 * ‖p‖ ^ 2 +       8 * (g ^ 2 + mu) * r ^ 2 * ‖q‖ ^ 2 + 8 * a ^ 2 * r ^ 2 * ‖s‖ ^ 2 +       (16 * a ^ 2 + 24 * (g ^ 2 + mu)) * r ^ 2 * mixed p s,     8 * a * g * r ^ 3 * (-‖p‖ ^ 2 + 2 * ‖s‖ ^ 2 + mixed p s),     2 * (g ^ 2 + mu) * r ^ 4 * (‖p‖ ^ 2 + 4 * ‖s‖ ^ 2 - 4 * mixed p s)]

**Theorem 1.46 (rawIntegrand parity pair).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawIntegrand_parity_pair (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :     rawIntegrand g mu a r p q s t =       2 * ‖value (rawA a r p 0 s) t + (g : ℂ) * value (rawB r p 0 s) t‖ ^ 2 +       2 * ‖value (rawA a r 0 q 0) t + (g : ℂ) * value (rawB r 0 q 0) t‖ ^ 2 +       2 * mu * (‖value (rawB r p 0 s) t‖ ^ 2 + ‖value (rawB r 0 q 0) t‖ ^ 2)

**Theorem 1.47 (rawIntegrand quartic).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rawIntegrand_quartic (g mu a r : ℝ) (p q s : ℂ) (t : ℝ) :     rawIntegrand g mu a r p q s t =       ∑ i : Fin 5, quarticCoeffs g mu a r p q s i * t ^ (i : ℕ)

**Theorem 1.48 (integral fin5 monomials).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma integral_fin5_monomials (b : Fin 5 → ℝ) :     (∫ t in (0 : ℝ)..1, ∑ i : Fin 5, b i * t ^ (i : ℕ)) =       ∑ i : Fin 5, b i / (((i : ℕ) : ℝ) + 1)

**Theorem 1.49 (raw pairedEnergy).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma raw_pairedEnergy (c : ℕ) (a r : ℝ) (p q s : ℂ) :     pairedEnergy c (rawA a r p q s) (rawB r p q s) =       U₃ (Real.pi / 4) (mean c) a r * ‖p‖ ^ 2 +       2 * O₃ (Real.pi / 4) (mean c) a r * ‖q‖ ^ 2 +       C₃ (Real.pi / 4) (mean c) a r * ‖s‖ ^ 2 +       2 * T₃ (Real.pi / 4) (mean c) a r * mixed p s

**Theorem 1.50 (mixed div real).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma mixed_div_real (p s : ℂ) (u v : ℝ) :     mixed (p / (u : ℂ)) (s / (v : ℂ)) = mixed p s / (u * v)

**Theorem 1.51 (norm div sqrt sq).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma norm_div_sqrt_sq (p : ℂ) {d : ℝ} (hd : 0 ≤ d) :     ‖p / (Real.sqrt d : ℂ)‖ ^ 2 = ‖p‖ ^ 2 / d

**Definition 1.52 (finiteForm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def finiteForm (g mu a r : ℝ) (x : Fin 3 → ℂ) : ℝ :=   U₃ g mu a r / 3 * ‖x 0‖ ^ 2 + O₃ g mu a r * ‖x 1‖ ^ 2 +     C₃ g mu a r / 6 * ‖x 2‖ ^ 2 +     2 * (T₃ g mu a r / Real.sqrt 18) * mixed (x 0) (x 2)

**Definition 1.53 (finiteMatrix).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def finiteMatrix (g mu a r : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=   !![((U₃ g mu a r / 3 : ℝ) : ℂ), 0, ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ);       0, (O₃ g mu a r : ℂ), 0;       ((T₃ g mu a r / Real.sqrt 18 : ℝ) : ℂ), 0, ((C₃ g mu a r / 6 : ℝ) : ℂ)]

**Theorem 1.54 (finiteMatrix form).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finiteMatrix_form (g mu a r : ℝ) (x : Fin 3 → ℂ) :     star x ⬝ᵥ (finiteMatrix g mu a r *ᵥ x) = (finiteForm g mu a r x : ℂ)

**Theorem 1.55 (finiteMatrix isHermitian).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finiteMatrix_isHermitian (g mu a r : ℝ) :     (finiteMatrix g mu a r).IsHermitian

**Theorem 1.56 (actual finite energy form).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_energy_form {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (x : Fin 3 → ℂ) :     pairedEnergy c         (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))         (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) =       finiteForm (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x

**Theorem 1.57 (actual finite matrix realization).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_matrix_realization {n : ℤ} (hn : n ≠ 0) (c N : ℕ) (hN : 0 < N)     (x : Fin 3 → ℂ) :     star x ⬝ᵥ (finiteMatrix (Real.pi / 4) (mean c)         (arithmeticBoundarySymbol c n) ((n : ℝ) / N) *ᵥ x) =       (pairedEnergy c         (reciprocalPolynomial 3 N (P c (threeNodes n) (sourceHead n x)))         (reciprocalPolynomial 3 N (Q (threeNodes n) (sourceHead n x))) : ℂ)

For either nonzero signed exterior node m, the actual nodal model and exact reciprocal evaluation give pi^2(1-(n/m)^2)^2 times the column norm square equal to the corresponding reciprocal numerator norm square divided by m^2.

The negative exterior node is proved to lie outside the literal head using the same radius |n|. After taking norm squares the positive and negative columns share a denominator, and their sum is precisely pairedTerm.

When N>0, |n|<N and m>N, the squared factors satisfy 0<(1-(n/N)^2)^2 <= (1-(n/m)^2)^2 <=1. These bounds depend on the nodes and cutoff, before any coefficient vector.

**Theorem 1.58 (actual single symmetric denominator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_single_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)     (hN : 0 < N) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) (hmS : m ∉ threeNodes n) :     Real.pi ^ 2 * (1 - ((n : ℝ) / (m : ℝ)) ^ 2) ^ 2 *         ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =       ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -           (arithmeticBoundarySymbol c m : ℂ) *             value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 /         (m : ℝ) ^ 2

**Theorem 1.59 (threeNodes radius).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma threeNodes_radius (n : ℤ) :     ∀ k ∈ threeNodes n, |(k : ℝ)| ≤ |(n : ℝ)|

**Theorem 1.60 (actual pair symmetric denominator).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_pair_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)     (hN : 0 < N) (hR : |(n : ℝ)| < (N : ℝ)) (v : ℤ → ℂ) (j : ℕ) :     Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *         pairedColumnTerm c N (threeNodes n) v j =       pairedTerm c N         (reciprocalPolynomial 3 N (P c (threeNodes n) v))         (reciprocalPolynomial 3 N (Q (threeNodes n) v)) j

**Theorem 1.61 (symmetric factor bounds).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma symmetric_factor_bounds {b N m : ℝ} (hN : 0 < N) (hR : |b| < N) (hNm : N < m) :     0 < (1 - (b / N) ^ 2) ^ 2 ∧       (1 - (b / N) ^ 2) ^ 2 ≤ (1 - (b / m) ^ 2) ^ 2 ∧       (1 - (b / m) ^ 2) ^ 2 ≤ 1

K_N is defined to be Matrix.gram Complex (sourceTailFamily hc N n) from the literal source family. It includes every j>=0 and both exterior signs. Its quadratic form is given by actual_source_gram_tsum.

Let delta=9*336*c^2*(1+log(c))^3, l_N=1-delta/N and u_N=(1+delta/N)/(1-(n/N)^2)^2. For c>=3, signed n!=0, N>=9 and |n|<N, the complete actual paired symbol bounds and exact denominator comparison yield l_N H_N <= pi^2 N K_N <= u_N H_N.

The vector form is proved for every complex x, including zero and cancellation, before the Loewner forms. Complete-tail summability holds by actual_tail_summable_all. No vector mass or finite energy is divided out.

The matrices in the two differences are Hermitian by the physical finite-matrix witness and the canonical Gram witness. Their nonnegative quadratic forms give positive semidefiniteness of the two actual differences.

**Definition 1.62 (delta336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def delta336 (c : ℕ) : ℝ := 9 * 336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3

**Definition 1.63 (lower336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def lower336 (c N : ℕ) : ℝ := 1 - delta336 c / N

**Definition 1.64 (upper336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def upper336 (c N : ℕ) (n : ℤ) : ℝ :=   (1 + delta336 c / N) / (1 - ((n : ℝ) / N) ^ 2) ^ 2

**Definition 1.65 (actualTailGram).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def actualTailGram {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=   Matrix.gram ℂ (sourceTailFamily hc N n)

**Theorem 1.66 (actual full336 all vector).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_full336_all_vector {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     ∀ x : Fin 3 → ℂ,       lower336 c N * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x ≤         Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ∧       Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ≤         upper336 c N n * finiteForm (Real.pi / 4) (mean c)           (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x

**Theorem 1.67 (actual full336 loewner).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_full336_loewner {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :     let H := finiteMatrix (Real.pi / 4) (mean c)       (arithmeticBoundarySymbol c n) ((n : ℝ) / N)     let K := actualTailGram hc n N     ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧       (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.C`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.O`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.T`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.U`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actualTailGram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_form`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_energy_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_finite_matrix_realization`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_all_vector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_full336_loewner`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_gram_posDef`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_pair_symmetric_denominator`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_raw_reciprocals`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_single_symmetric_denominator`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_symbol_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.actual_three_nodal`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientGram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.coefficientInner`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.delta336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.evenDet`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.exceptional_trace_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteForm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_form`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finiteMatrix_isHermitian`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.finite_trace_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headE`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headO`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.headS`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.integral_fin5_monomials`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.lower336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.mixed_div_real`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodeVector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.nodes_distinct`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.norm_div_sqrt_sq`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairSpace`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnLp`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.pairedColumnVector`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.quarticCoeffs`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawA`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawB`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawHead_nodes`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_parity_pair`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.rawIntegrand_quartic`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.raw_pairedEnergy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.reciprocal_three`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.singletonHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceColumnMap`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_eq_rawHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceHead_original_norm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.sourceTailFamily`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.source_linear_combination`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.symmetric_factor_bounds`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.tailSpace`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_card`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.threeNodes_radius`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSourceHeadBridge.upper336`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualExplicit336](ActualExplicit336.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalCoercivity](ActualNodalCoercivity.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure](ActualNodalTailEnclosure.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualPairedReciprocal](ActualPairedReciprocal.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail](ActualUniformFiniteHeadTail.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolResonance](PrimeSymbolResonance.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram](WeilArithmeticCouplingParityGram.md)
