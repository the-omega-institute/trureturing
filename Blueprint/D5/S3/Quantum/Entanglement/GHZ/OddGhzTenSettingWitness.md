# The ten-setting GHZ witness in odd dimensions

## Abstract

The ten-setting GHZ witness bounds fidelity and genuine multipartite Schmidt dimension in every odd local dimension.

Fin d indexes coordinates from zero. Three-party coordinates use Fin d × (Fin d × Fin d). The symbols alpha, beta, psi, rho and sigma denote the corresponding Lean type and vector variables. Complex.ofReal and Nat.cast display scalar embeddings; all divisions in Complex or Real are field divisions, while Nat.mod and Nat.sub retain natural remainder and truncated subtraction. Pi.single is the coordinate delta vector. Matrix.vecMulVec, Matrix.kroneckerMap, Matrix.mulVec, dotProduct and star have their usual Lean meanings. The density states are D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState; CStarMatrix.ofMatrix.symm reads their underlying matrices. Nine labelled settings are summed with multiplicity, including when d = 1.

**Definition 1.1 (Ensemble).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall rho \in Matrix\left((Fin\left(p\right)\times Fin\left(q\right)), (Fin\left(p\right)\times Fin\left(q\right)), Complex\right),\; Ensemble\left(rho\right) = \{N:Nat;weight:Fin\left(N\right) \to Real;nonneg:\forall i \in Fin\left(N\right),\; 0 \le weight\left(i\right);le_{one}:\forall i \in Fin\left(N\right),\; weight\left(i\right) \le 1;total:\sum_{{i:Fin\left(N\right)}}(weight\left(i\right)) = 1;psi:Fin\left(N\right) \to \left((Fin\left(p\right)\times Fin\left(q\right)) \to Complex\right);unit:\forall i \in Fin\left(N\right),\; \sum_{{x:(Fin\left(p\right)\times Fin\left(q\right))}}(\Vert psi\left(i\right)\left(x\right)\Vert^{2}) = 1;average:\sum_{{i:Fin\left(N\right)}}(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(weight\left(i\right)\right), \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(psi\left(i\right)\right)\right)) = rho\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.Ensemble` (`✓ std3`).

*Citation.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

The dependent record has fields N, weight, nonneg, le_one, total, psi, unit and average. Page 18: “Let ρAB be a density matrix acting on CᵖA ⊗ CᑫB, where pq = n. Let Sρ = {{pi, |ψi⟩ : i = 1, 2, ..., N} : ρAB = ∑ⁿᵢ₌₁ pi|ψi⟩AB⟨ψi|, where |ψi⟩AB ∈ CᵖA ⊗ CᑫB, 0 ≤ pi ≤ 1 and ∑ᴺᵢ₌₁ pi = 1}.” The reconstruction is read over N ensemble terms and uses Euclidean unit vectors.

**Theorem 1.2 (The quadratic form of a rank-one density matrix).**

$$\forall n \in Type,\; [Fintype\left(n\right)] \forall z \in n \to Complex,\; \forall psi \in n \to Complex,\; dotProduct\left(star\left(z\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(psi\right), z\right)\right) = \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Complex}.\operatorname{normSq}\left(dotProduct\left(star\left(z\right), psi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.quadratic_projector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex vectors on a finite index type, the quadratic form of PureStateHandshake.rankOneDensity equals the complex embedding of the squared overlap norm.

**Theorem 1.3 (A convex weight is at most one).**

$$\forall iota \in Type,\; [Fintype\left(iota\right)] [DecidableEq\left(iota\right)] \forall weight \in iota \to Real,\; (\forall j \in iota,\; 0 \le weight\left(j\right)) \Rightarrow ((\sum_{{j:iota}}(weight\left(j\right)) = 1) \Rightarrow (\forall i \in iota,\; weight\left(i\right) \le 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.weight_le_one_of_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative weight in a finite family with total one is at most one.

**Theorem 1.4 (A density matrix has a finite unit-vector ensemble).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall rho \in Matrix\left((Fin\left(p\right)\times Fin\left(q\right)), (Fin\left(p\right)\times Fin\left(q\right)), Complex\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \Rightarrow (Nonempty\left(Ensemble\left(rho\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.spectral_ensemble_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Samuel L. Braunstein; Sibasish Ghosh; Simone Severini (2006). *The Laplacian of a graph as a density matrix: a basic combinatorial approach to separability of mixed states*. DOI: [10.1007/s00026-006-0289-3](https://doi.org/10.1007/s00026-006-0289-3). URL: <https://arxiv.org/abs/quant-ph/0406165v2>.

*Commentary.*

Every positive semidefinite complex matrix on Fin p × Fin q with trace one has an Ensemble. Eigenvalues give the weights and an orthonormal eigenbasis gives the unit vectors.

**Definition 1.5 (Pure-state Schmidt rank).**

$$\forall alpha \in Type,\; \forall beta \in Type,\; [Fintype\left(beta\right)] \forall v \in (alpha\times beta) \to Complex,\; schmidtRank\left(v\right) = \operatorname{Matrix}.\operatorname{rank}\left(\operatorname{Matrix}.\operatorname{of}\left((\lambda i:alpha, (\lambda j:beta, v\left((i,j)\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.schmidtRank` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Printed page 3: “The Schmidt rank is the rank of the reduced density matrix, which is necessarily equal to one for a product state but larger for pure entangled states (it generalizes to the Schmidt number for mixed states [33]).” The coefficient-matrix rank expresses this pure-state rank.

**Definition 1.6 (The exponential phase).**

$$\forall d \in Nat,\; omega\left(d\right) = \operatorname{Complex}.\operatorname{exp}\left(\frac{2 \cdot \operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{pi}\right) \cdot \operatorname{Complex}.\operatorname{I}}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.omega` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, uses the phase ω = exp(2πi/d).

**Definition 1.7 (Quadratic-phase basis vectors).**

$$\forall d \in Nat,\; \forall j \in Nat,\; \forall l \in Nat,\; basisVec\left(d, j, l\right) = (\lambda m:Fin\left(d\right), \frac{1}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Nat}.\operatorname{cast}\left(d\right)\right)\right)} \cdot omega\left(d\right)^{\operatorname{Fin}.\operatorname{val}\left(m\right) \cdot \left(l + j \cdot \operatorname{Fin}.\operatorname{val}\left(m\right)\right)})$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.basisVec` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, gives |e_l^(j)⟩ = d^(-1/2) Σ_m ω^(m(l+jm)) |m⟩. Here ω is exp(2πi/d), and the formula gives each coordinate.

**Definition 1.8 (The rank-one projector).**

$$\forall d \in Nat,\; \forall v \in Fin\left(d\right) \to Complex,\; proj\left(v\right) = \operatorname{Matrix}.\operatorname{vecMulVec}\left(v, star\left(v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.proj` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

The projector |v⟩⟨v| is Matrix.vecMulVec v (star v).

**Definition 1.9 (The nine product settings).**

$$\forall d \in Nat,\; tuples\left(d\right) = [(0,0,0),(1,1,\operatorname{Nat}.\operatorname{sub}\left(d, 2\right)),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),2),(0,1,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right)),(1,0,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right)),(0,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),1),(1,\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),0),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),0,1),(\operatorname{Nat}.\operatorname{sub}\left(d, 1\right),1,0)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.tuples` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, equation (V1), lists the nine triples in the displayed order. A List retains every label when entries coincide.

**Definition 1.10 (The ten-setting operator).**

$$\forall d \in Nat,\; witness\left(d\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Nat}.\operatorname{cast}\left(3\right), \sum_{{l:Fin\left(d\right)}}(\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), proj\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), proj\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right), proj\left(\operatorname{Pi}.\operatorname{single}\left(l, 1\right)\right)\right)\right))\right) + \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\lambda j:(Nat\times (Nat\times Nat)), \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda l:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), \operatorname{Nat}.\operatorname{mod}\left(\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(l\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right), d\right) = 0), \operatorname{Finset}.\operatorname{univ}:Finset\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right)\right), (\lambda l:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), proj\left(basisVec\left(d, \operatorname{Prod}.\operatorname{fst}\left(j\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(l\right)\right)\right)\right), \operatorname{Matrix}.\operatorname{kroneckerMap}\left((\lambda x:Complex, (\lambda y:Complex, x \cdot y)), proj\left(basisVec\left(d, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(j\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right)\right)\right), proj\left(basisVec\left(d, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(j\right)\right), \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(l\right)\right)\right)\right)\right)\right)\right))\right)), tuples\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witness` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22: “Based on these measurements, we define the entanglement witness operator”. Equation (V2) weights the computational measurement by three and each of the nine quadratic-phase measurements by one. The modular condition is Nat.mod of the coordinate-index sum equal to zero.

**Definition 1.11 (The three-party GHZ vector).**

$$\forall d \in Nat,\; ghz\left(d\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\frac{1}{\operatorname{Complex}.\operatorname{ofReal}\left(\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{Nat}.\operatorname{cast}\left(d\right)\right)\right)}, \sum_{{i:Fin\left(d\right)}}(\operatorname{Pi}.\operatorname{single}\left((i,i,i), 1\right):(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Equation (5) specializes to the normalized sum of the coordinates (i,i,i) for three parties.

**Definition 1.12 (The measured expectation).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; witnessValue\left(d, rho\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(witness\left(d\right) \cdot \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witnessValue` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22: “The corresponding entanglement witness quantity is therefore W_d = tr(𝒲_d ρ).” The real part of this trace is explicit.

**Definition 1.13 (GHZ fidelity).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; ghzFidelity\left(d, rho\right) = \operatorname{Complex}.\operatorname{re}\left(dotProduct\left(star\left(ghz\left(d\right)\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right), ghz\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghzFidelity` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

The GHZ fidelity is the real part of the matrix expectation in the normalized three-party GHZ vector.

**Definition 1.14 (Schmidt rank across each cut).**

$$\forall d \in Nat,\; \forall k \in Fin\left(3\right),\; \forall psi \in (Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex,\; cutRank\left(k, psi\right) = if \operatorname{Fin}.\operatorname{val}\left(k\right) = 0 then schmidtRank\left((\lambda p:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), psi\left((\operatorname{Prod}.\operatorname{fst}\left(p\right),\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right),\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))\right))\right) else if \operatorname{Fin}.\operatorname{val}\left(k\right) = 1 then schmidtRank\left((\lambda p:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), psi\left((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right),\operatorname{Prod}.\operatorname{fst}\left(p\right),\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))\right))\right) else schmidtRank\left((\lambda p:(Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))), psi\left((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right),\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right),\operatorname{Prod}.\operatorname{fst}\left(p\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.cutRank` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

The three cuts separate party zero, one or two from the other two parties; each coefficient array retains the other two indices in their original order.

**Definition 1.15 (Bounded Schmidt number).**

$$\forall d \in Nat,\; \forall k \in Fin\left(3\right),\; \forall r \in Nat,\; \forall sigma \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; SchmidtNumberLE\left(k, r, sigma\right) \Leftrightarrow (\exists m \in Nat,\; \exists p \in Fin\left(m\right) \to Real,\; \exists psi \in Fin\left(m\right) \to \left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right))) \to Complex\right),\; (\forall i \in Fin\left(m\right),\; 0 \le p\left(i\right)) \land ((\sum_{{i:Fin\left(m\right)}}(p\left(i\right)) = 1) \land ((\forall i \in Fin\left(m\right),\; dotProduct\left(star\left(psi\left(i\right)\right), psi\left(i\right)\right) = 1) \land ((\forall i \in Fin\left(m\right),\; cutRank\left(k, psi\left(i\right)\right) \le r) \land (\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(sigma.1\right) = \sum_{{i:Fin\left(m\right)}}(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(p\left(i\right)\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(psi\left(i\right), star\left(psi\left(i\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.SchmidtNumberLE` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

A finite convex decomposition into unit vectors whose Schmidt ranks across the chosen cut are at most r defines Schmidt number at most r.

**Definition 1.16 (Mixtures over the three cuts).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; \forall r \in Nat,\; GMEDecomposable\left(r, rho\right) \Leftrightarrow (\exists q \in Fin\left(3\right) \to Real,\; \exists sigma \in Fin\left(3\right) \to DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (\forall k \in Fin\left(3\right),\; 0 \le q\left(k\right)) \land ((\sum_{{k:Fin\left(3\right)}}(q\left(k\right)) = 1) \land ((\forall k \in Fin\left(3\right),\; SchmidtNumberLE\left(k, r, sigma\left(k\right)\right)) \land (\operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right) = \sum_{{k:Fin\left(3\right)}}(\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Complex}.\operatorname{ofReal}\left(q\left(k\right)\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(sigma\left(k\right).1\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.GMEDecomposable` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2). It minimizes over mixtures across bipartitions. Every branch has Schmidt number at most r; weights are nonnegative and sum to one.

**Definition 1.17 (Genuine multipartite Schmidt dimension).**

$$\forall d \in Nat,\; \forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; gmeDim\left(rho\right) = sInf\left(\{r:Nat|GMEDecomposable\left(r, rho\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.gmeDim` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Definition 1, printed page 3: “For an arbitrary n-partite state ρ, its GME-dimension is” followed by equation (2), the minimum of the admissible rank bounds. The natural infimum is attained: a spectral decomposition shows that r = d is admissible for every density state.

**Definition 1.18 (The all-odd-dimensional inequalities).**

$$claim \Leftrightarrow (\forall d \in Nat,\; (Odd\left(d\right)) \Rightarrow (\forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (witnessValue\left(d, rho\right) \le 3 + \frac{9 \cdot \operatorname{Nat}.\operatorname{cast}\left(gmeDim\left(rho\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}) \land (\frac{witnessValue\left(d, rho\right) - 3}{9} \le ghzFidelity\left(d, rho\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.claim` (`✓ std3`).

*Citation.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Supplementary V, printed page 22, equations (V3)–(V5): “We have shown this explicitly for odd d ≤ 17 and conjecture it to hold for odd d in general.” The universal statement includes every odd natural d, every density state, both the GME-dimension bound (V3) and the fidelity bound (V4). Oddness implies d is positive. Composite dimensions and d = 1 are included.

**Theorem 1.19 (Both bounds hold for every odd dimension).**

$$\forall d \in Nat,\; (Odd\left(d\right)) \Rightarrow (\forall rho \in DensityState\left((Fin\left(d\right)\times (Fin\left(d\right)\times Fin\left(d\right)))\right),\; (witnessValue\left(d, rho\right) \le 3 + \frac{9 \cdot \operatorname{Nat}.\operatorname{cast}\left(gmeDim\left(rho\right)\right)}{\operatorname{Nat}.\operatorname{cast}\left(d\right)}) \land (\frac{witnessValue\left(d, rho\right) - 3}{9} \le ghzFidelity\left(d, rho\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. Cobucci, A. Tavakoli (2024). *Detecting the dimensionality of genuine multi-particle entanglement*. DOI: [10.1126/sciadv.adq4467](https://doi.org/10.1126/sciadv.adq4467). URL: <https://arxiv.org/abs/2402.06234>.

*Commentary.*

Additive-character orthogonality makes the operator block diagonal in the two coordinate differences. Each nonzero difference block has at most three labelled settings at a fixed frequency: oddness makes multiplication by two cancellable, and the three signed values of any nonzero difference are distinct. Cyclic Parseval then bounds these blocks by three. The zero-difference block contributes the GHZ overlap with coefficient nine and the norm with coefficient three. A spectral decomposition extends the quadratic bound to density states. The coefficient-matrix trace bound gives fidelity at most r/d for pure states of cut rank at most r, and convexity extends it to mixtures across all three cuts. Combining these estimates proves both inequalities. Mutual unbiasedness is not used. Attainment of the non-GHZ upper bound in every odd dimension and even dimensions remain open here.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.Ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.GMEDecomposable`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.SchmidtNumberLE`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.basisVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.cutRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghz`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.ghzFidelity`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.gmeDim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.omega`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.proj`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.quadratic_projector`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.schmidtRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.spectral_ensemble_nonempty`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.tuples`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.weight_le_one_of_total`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.witnessValue`
- Dependency: [D5/S3/Fourier/FullBispectrumStability](../../../Fourier/FullBispectrumStability.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../QuantumChannels/TomiyamaDiagonalKPositivity.md)
