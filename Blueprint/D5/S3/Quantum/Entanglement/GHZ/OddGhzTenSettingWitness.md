# The ten-setting GHZ witness in odd dimensions

## Abstract

The ten-setting GHZ witness bounds fidelity and genuine multipartite Schmidt dimension in every odd local dimension.

**Theorem 1.1 (Finite spectral ensembles).**

$$\forall (\iota: Type), ([Fintype\left(\iota\right)], ([DecidableEq\left(\iota\right)], (\forall (\rho: DensityState\left(\iota\right)), (\exists (m: Nat), (\exists (p: Fin\left(m\right) \to Real), (\exists (\psi: Fin\left(m\right) \to \left(\iota \to Complex\right)), ((\forall (i: Fin\left(m\right)), (0 \le p\left(i\right))) \land ((\sum_{i: Fin\left(m\right)} (p\left(i\right)) = 1) \land ((\forall (i: Fin\left(m\right)), (dotProduct\left(star\left(\psi\left(i\right)\right), \psi\left(i\right)\right) = 1)) \land (\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(\operatorname{Subtype}.\operatorname{val}\left(\rho\right)\right) = \sum_{i: Fin\left(m\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(p\left(i\right)\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(\psi\left(i\right), star\left(\psi\left(i\right)\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.density_ensemble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite-dimensional density matrix is a convex sum of rank-one matrices of unit vectors. The real weights are nonnegative and sum to one; Complex.ofReal displays their inclusion into the complex matrix scalars.

**Theorem 1.2 (Real scaling of a quadratic form).**

$$\forall (\iota: Type), ([Fintype\left(\iota\right)], (\forall (g: \iota \to Complex), (\forall (r: Real), (\forall (A: Matrix\left(\iota, \iota, Complex\right)), (\operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(g\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(r\right), A\right), g\right)\right)\right) = r \cdot \operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(g\right), \operatorname{Matrix}.\operatorname{mulVec}\left(A, g\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.quadratic_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part of a complex quadratic form scales by a real scalar r. Complex.ofReal displays the scalar used to multiply the matrix.

**Theorem 1.3 (Symmetry of squared overlaps).**

$$\forall (\iota: Type), ([Fintype\left(\iota\right)], (\forall (f: \iota \to Complex), (\forall (g: \iota \to Complex), (\operatorname{Complex}.\operatorname{normSq}\left(dotProduct\left(star\left(f\right), g\right)\right) = \operatorname{Complex}.\operatorname{normSq}\left(dotProduct\left(star\left(g\right), f\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.normSq_overlap_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging two finite complex vectors conjugates their overlap and preserves its squared absolute value.

**Theorem 1.4 (Squared overlap with the GHZ vector).**

$$\forall (d: Nat), (\forall (v: (Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex), (\operatorname{Complex}.\operatorname{normSq}\left(dotProduct\left(star\left(ghz\left(d\right)\right), v\right)\right) = \frac{1}{\operatorname{Nat}.\operatorname{cast}\left(d\right)} \cdot \operatorname{Complex}.\operatorname{normSq}\left(\sum_{i: Fin\left(d\right)} (v\left((i,i,i)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz_overlap_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension d and every three-party complex vector v, the squared GHZ overlap is one over d times the squared absolute value of the sum of diagonal coordinates. Field division includes d = 0.

Fin d indexes coordinates from zero. Three-party coordinates use Fin d × (Fin d × Fin d). The symbols psi, rho and sigma denote the corresponding Lean vector and state variables. Complex.ofReal and Nat.cast display scalar embeddings; all divisions in Complex or Real are field divisions, while Nat.mod and Nat.sub retain natural remainder and truncated subtraction. Pi.single is the coordinate delta vector. Matrix.vecMulVec, Matrix.kroneckerMap, Matrix.mulVec, dotProduct and star have their usual Lean meanings. The density states are D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState; CStarMatrix.ofMatrix.symm reads their underlying matrices. Nine labelled settings are summed with multiplicity, including when d = 1.

FormationBounds.spectral_ensemble_nonempty supplies a finite convex ensemble for each positive semidefinite trace-one coefficient matrix. Its Ensemble record stores the weights, Euclidean unit vectors and rank-one reconstruction.

Pure-state Schmidt rank is the rank of the coefficient matrix. The three-party cuts keep the other two indices in Fin d × Fin d. Supplementary V, printed page 22, uses the phase ω = exp(2πi/d), represented by WindowRegister.windowRoot.

$$
\forall d \in Nat,\; \operatorname{WindowRegister}.\operatorname{windowRoot}\left(d\right) = \operatorname{Complex}.\operatorname{exp}\left(\frac{2 \cdot \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{pi}\right) \cdot \operatorname{Complex}.\operatorname{I}}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}\right)
$$

**Definition 1.5 (Quadratic-phase basis vectors).**

$$\forall d \in Nat,\; \forall j \in Nat,\; \forall l \in Nat,\; basisVec\left(d, j, l\right) = (\lambda m:Fin\left(d\right), \frac{1}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Nat}.\operatorname{cast}\left(d\right)\right)\right)} \cdot \operatorname{WindowRegister}.\operatorname{windowRoot}\left(d\right)^{\operatorname{Fin}.\operatorname{val}\left(m\right) \cdot \left(l + j \cdot \operatorname{Fin}.\operatorname{val}\left(m\right)\right)})$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.basisVec` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, gives |e_l^(j)⟩ = d^(-1/2) Σ_m ω^(m(l+jm)) |m⟩. Here ω is exp(2πi/d), and the formula gives each coordinate.

The projector |v⟩⟨v| is PureStateHandshake.rankOneDensity v, whose entries are v_i conjugate(v_j).

$$
\forall d \in Nat,\; \forall v \in Fin\left(d\right) \to Complex,\; \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(v\right) = \operatorname{Matrix}.\operatorname{vecMulVec}\left(v, star\left(v\right)\right)
$$

**Definition 1.6 (The nine product settings).**

$$\forall d \in Nat,\; tuples\left(d\right) = [(0,0,0),(1,1,\operatorname{Nat}.\operatorname{sub}\left(d, 2\right)),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),2),(0,1,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right)),(1,0,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right)),(0,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),1),(1,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),0),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),0,1),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),1,0)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.tuples` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, equation (V1), lists the nine triples in the displayed order. A List retains every label when entries coincide.

**Definition 1.7 (The ten-setting operator).**

$$\forall d \in Nat,\; witness\left(d\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Nat}.\operatorname{cast}\left(3\right), \sum_{{l:Fin\left(d\right)}}(\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right)\right)\right))\right) + \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\lambda j:(Nat\times (Nat\times Nat)), \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda l:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), \operatorname{Nat}.\operatorname{mod}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(l\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right), d\right) = 0), \operatorname{Finset}.\operatorname{univ}:Finset\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right)\right), (\lambda l:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(basisVec\left(d, \operatorname{Prod}.\operatorname{fst}\left(j\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(l\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(basisVec\left(d, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(j\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right)\right)\right), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(basisVec\left(d, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(j\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right)\right)\right)\right)\right))\right)), tuples\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witness` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22: “Based on these measurements, we define the entanglement witness operator”. Equation (V2) weights the computational measurement by three and each of the nine quadratic-phase measurements by one. The modular condition is Nat.mod of the coordinate-index sum equal to zero.

**Definition 1.8 (The three-party GHZ vector).**

$$\forall d \in Nat,\; ghz\left(d\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\frac{1}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Nat}.\operatorname{cast}\left(d\right)\right)\right)}, \sum_{{i:Fin\left(d\right)}}(\operatorname{Pi}.\operatorname{single}\left((i,i,i), 1\right):(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Equation (5) specializes to the normalized sum of the coordinates (i,i,i) for three parties.

Supplementary V, printed page 22, defines W_d = tr(𝒲_d ρ). Its real expectation is GHZMeasureBiseparableBound.expect applied to the state matrix and witness operator.

$$
\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; W\left(d, rho\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right)
$$

The GHZ fidelity is the real matrix expectation in the normalized three-party GHZ vector, represented by RHLinalg.hermForm.

$$
\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; F\left(d, rho\right) = \operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(ghz\left(d\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right), ghz\left(d\right)\right)\right)\right)
$$

**Definition 1.9 (Schmidt rank across each cut).**

$$\forall d \in Nat,\; \forall k \in Fin\left(3\right),\; \forall psi \in (Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex,\; cutRank\left(k, psi\right) = if \operatorname{Fin}.\operatorname{val}\left(k\right) = 0 then \operatorname{Matrix}.\operatorname{rank}\left(\operatorname{Matrix}.\operatorname{of}\left((\lambda i:Fin\left(d\right), (\lambda j:(Fin\left(d\right)\times Fin\left(d\right)), psi\left((i,\operatorname{Prod}.\operatorname{fst}\left(j\right),\operatorname{Prod}.\operatorname{snd}\left(j\right))\right)))\right)\right) else if \operatorname{Fin}.\operatorname{val}\left(k\right) = 1 then \operatorname{Matrix}.\operatorname{rank}\left(\operatorname{Matrix}.\operatorname{of}\left((\lambda i:Fin\left(d\right), (\lambda j:(Fin\left(d\right)\times Fin\left(d\right)), psi\left((\operatorname{Prod}.\operatorname{fst}\left(j\right),i,\operatorname{Prod}.\operatorname{snd}\left(j\right))\right)))\right)\right) else \operatorname{Matrix}.\operatorname{rank}\left(\operatorname{Matrix}.\operatorname{of}\left((\lambda i:Fin\left(d\right), (\lambda j:(Fin\left(d\right)\times Fin\left(d\right)), psi\left((\operatorname{Prod}.\operatorname{fst}\left(j\right),\operatorname{Prod}.\operatorname{snd}\left(j\right),i)\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.cutRank` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

The three cuts separate party zero, one or two from the other two parties. Each Schmidt rank is the rank of the coefficient matrix with row index in Fin d and column index in Fin d × Fin d, in the displayed index order.

**Definition 1.10 (Bounded Schmidt number).**

$$\forall d \in Nat,\; \forall k \in Fin\left(3\right),\; \forall r \in Nat,\; \forall sigma \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; SchmidtNumberLE\left(k, r, sigma\right) \Leftrightarrow (\exists m \in Nat,\; \exists p \in Fin\left(m\right) \to Real,\; \exists psi \in Fin\left(m\right) \to \left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex\right),\; (\forall i \in Fin\left(m\right),\; 0 \le p\left(i\right)) \land ((\sum_{{i:Fin\left(m\right)}}(p\left(i\right)) = 1) \land ((\forall i \in Fin\left(m\right),\; dotProduct\left(star\left(psi\left(i\right)\right), psi\left(i\right)\right) = 1) \land ((\forall i \in Fin\left(m\right),\; cutRank\left(k, psi\left(i\right)\right) \le r) \land (\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(sigma.1\right) = \sum_{{i:Fin\left(m\right)}}(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(p\left(i\right)\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(psi\left(i\right), star\left(psi\left(i\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.SchmidtNumberLE` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

A finite convex decomposition into unit vectors whose Schmidt ranks across the chosen cut are at most r defines Schmidt number at most r.

**Definition 1.11 (Mixtures over the three cuts).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; \forall r \in Nat,\; GMEDecomposable\left(r, rho\right) \Leftrightarrow (\exists q \in Fin\left(3\right) \to Real,\; \exists sigma \in Fin\left(3\right) \to DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (\forall k \in Fin\left(3\right),\; 0 \le q\left(k\right)) \land ((\sum_{{k:Fin\left(3\right)}}(q\left(k\right)) = 1) \land ((\forall k \in Fin\left(3\right),\; SchmidtNumberLE\left(k, r, sigma\left(k\right)\right)) \land (\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right) = \sum_{{k:Fin\left(3\right)}}(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(q\left(k\right)\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(sigma\left(k\right).1\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.GMEDecomposable` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2). It minimizes over mixtures across bipartitions. Every branch has Schmidt number at most r; weights are nonnegative and sum to one.

**Definition 1.12 (Genuine multipartite Schmidt dimension).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; gmeDim\left(rho\right) = sInf\left(\{r:Nat|GMEDecomposable\left(r, rho\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.gmeDim` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2), the minimum of the admissible rank bounds. The natural infimum is attained: a spectral decomposition shows that r = d is admissible for every density state.

**Definition 1.13 (The all-odd-dimensional inequalities).**

$$claim \Leftrightarrow (\forall d \in Nat,\; (Odd\left(d\right)) \Rightarrow (\forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right) \le 3 + \frac{9 \cdot \operatorname{Nat}.\operatorname{cast}\left(gmeDim\left(rho\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}) \land (\frac{\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right) - 3}{9} \le \operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(ghz\left(d\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right), ghz\left(d\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.claim` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, equations (V3)–(V5): “We have shown this explicitly for odd d ≤ 17 and conjecture it to hold for odd d in general.” The universal statement includes every odd natural d, every density state, both the GME-dimension bound (V3) and the fidelity bound (V4). Oddness implies d is positive. Composite dimensions and d = 1 are included.

**Theorem 1.14 (Both bounds hold for every odd dimension).**

$$\forall d \in Nat,\; (Odd\left(d\right)) \Rightarrow (\forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right) \le 3 + \frac{9 \cdot \operatorname{Nat}.\operatorname{cast}\left(gmeDim\left(rho\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}) \land (\frac{\operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right) - 3}{9} \le \operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(ghz\left(d\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right), ghz\left(d\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result` (`✓ std3`). ∎

*Resolves.* `Problems/cobucci-tavakoli-2024-odd-ghz-ten-setting-witness` (proved) by `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cobucci-tavakoli-2024-odd-ghz-ten-setting-witness","declaration_gid":"D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Additive-character orthogonality makes the operator block diagonal in the two coordinate differences. Each nonzero difference block has at most three labelled settings at a fixed frequency: oddness makes multiplication by two cancellable, and the three signed values of any nonzero difference are distinct. Cyclic Parseval then bounds these blocks by three. The zero-difference block contributes the GHZ overlap with coefficient nine and the norm with coefficient three. A spectral decomposition extends the quadratic bound to density states. The coefficient-matrix trace bound gives fidelity at most r/d for pure states of cut rank at most r, and convexity extends it to mixtures across all three cuts. Combining these estimates proves both inequalities. Mutual unbiasedness is not used. Attainment of the non-GHZ upper bound in every odd dimension and even dimensions remain open here.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.GMEDecomposable`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.SchmidtNumberLE`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.basisVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.cutRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.density_ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz_overlap_normSq`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.gmeDim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.normSq_overlap_comm`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.quadratic_smul`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.tuples`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witness`
- Dependency: [D5/S3/Fourier/FullBispectrumStability](../../../Fourier/FullBispectrumStability.md)
- Dependency: [D5/S3/Observer/WindowRegister](../../../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](../GraphDensity/FormationBounds.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../QuantumChannels/TomiyamaDiagonalKPositivity.md)
