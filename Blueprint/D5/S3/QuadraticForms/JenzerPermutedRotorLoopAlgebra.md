# JenzerPermutedRotorLoopAlgebra

## Abstract

Native scalar traces and ordered Clifford products.

**Definition 1.1 (Native scalar coefficient).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (x : \operatorname{CliffordAlgebra}\left(q\right)), \operatorname{scalarProjection}\left(q, x\right) = (\operatorname{ExteriorAlgebra}.\operatorname{algebraMapInv}\left(\operatorname{CliffordAlgebra}.\operatorname{equivExterior}\left(q, x\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.scalarProjection` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.1, page 8: “For $x = \sum_{A} x_{A} e_{A} \in \mathcal {C}$, $\langle x \rangle_{0} : = x_{\emptyset} \in \mathbb{R}$ is called the scalar part of $x$; the map $\langle \cdot \rangle_{0} : \mathcal {C} \to \mathbb{R}$ is the scalar projection or grade-0 projection. It is linear.” The linear Clifford-to-exterior equivalence reads this coefficient; multiplication is the Clifford product.

**Definition 1.2 (Homogeneous bivectors).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (x : \operatorname{CliffordAlgebra}\left(q\right)), \operatorname{IsBivector}\left(q, x\right) = (\operatorname{CliffordAlgebra}.\operatorname{equivExterior}\left(q, x\right) \in (\operatorname{ExteriorAlgebra}.\operatorname{exteriorPower}\left(\mathbb{R}, 2, V\right)))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.IsBivector` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Section 2.1, page 8: “We call $e_{A}$ a basis blade of grade $r = \lvert A \rvert$.” A bivector belongs to the homogeneous exterior power of degree two under the linear exterior equivalence.

**Definition 1.3 (Anticommuting unit bivectors).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \operatorname{AnticommutingUnitFamily}\left(q, k, B\right) = ((\forall (i : \operatorname{Fin}\left(k\right)), \operatorname{IsBivector}\left(q, B\left(i\right)\right)) \land ((\forall (i : \operatorname{Fin}\left(k\right)), (B\left(i\right))^{2} = (-(1))) \land (\forall (i : \operatorname{Fin}\left(k\right)), \forall (j : \operatorname{Fin}\left(k\right)), (i \ne (j)) \Rightarrow ((B\left(i\right)) \cdot (B\left(j\right)) = (-((B\left(j\right)) \cdot (B\left(i\right))))))))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.AnticommutingUnitFamily` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D3.2, page 10: “A family B₁, …, Bₖ of bivectors of a real Clifford algebra is called an anticommuting unit family of type −1 if Bᵢ² = −1 (1 ≤ i ≤ k), BᵢBⱼ = −BⱼBᵢ (i ≠ j).” The source set is represented by Fin k through the increasing map i ↦ i + 1.

**Definition 1.4 (Increasing subset product).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{subsetProduct}\left(B, S\right) = ((((S).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod})$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.subsetProduct` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.4, page 9: “Let $B_{1} ,   ... ,   B_{k} \in \mathcal {C}$ be given. For $S = \{ i_{1} < i_{2} < \cdot\cdot\cdot < i_{m} \} \subseteq \{ 1 , ... , k \}$ we set $B_{S} : = B_{i_{1}} B_{i_{2}} \cdot\cdot\cdot B_{i_{m}} ,   B_{\emptyset} : = 1$. The factors always stand in ascending index order.” List.prod of the empty list is one.

**Definition 1.5 (The star condition).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \operatorname{StarCondition}\left(B\right) = (\forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), ((S).\operatorname{Nonempty}) \Rightarrow (\operatorname{scalarProjection}\left(q, \operatorname{subsetProduct}\left(B, S\right)\right) = (0)))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.StarCondition` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D3.3, page 10: “An anticommuting unit family satisfies the star condition if $\langle B_{S} \rangle_{0} = 0$ for all $S \neq \emptyset$.” This predicate is not a hypothesis of the formula below.

**Definition 1.6 (Half-angle cosine).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (i : \operatorname{Fin}\left(k\right)), \operatorname{c}\left(theta, i\right) = (\operatorname{Real}.\operatorname{cos}\left(\frac{theta\left(i\right)}{2}\right))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.c` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.4, page 9: “We write throughout cᵢ := cos(θᵢ/2), sᵢ := sin(θᵢ/2), wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. Each coefficient uses the indexed real angle.

**Definition 1.7 (Half-angle sine).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (i : \operatorname{Fin}\left(k\right)), \operatorname{s}\left(theta, i\right) = (\operatorname{Real}.\operatorname{sin}\left(\frac{theta\left(i\right)}{2}\right))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.s` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.4, page 9: “We write throughout cᵢ := cos(θᵢ/2), sᵢ := sin(θᵢ/2), wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. Each coefficient uses the indexed real angle.

**Definition 1.8 (Sine-square weights).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (i : \operatorname{Fin}\left(k\right)), \operatorname{w}\left(theta, i\right) = ((\operatorname{s}\left(theta, i\right))^{2})$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.w` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.4, page 9: “wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. The definition is the square of the sine coefficient.

**Definition 1.9 (Subset expansion coefficient).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{a}\left(theta, S\right) = ((\prod_{i \in S} (\operatorname{s}\left(theta, i\right))) \cdot (\prod_{i \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)} (\operatorname{c}\left(theta, i\right))))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.a` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.4, page 9: “and for a subset $S$ $a_{S} : = \prod_{i \in S} s_{i} \prod_{i \neg\in S} c_{i}$.” Complements are taken in Fin k.

**Definition 1.10 (Trigonometric rotor).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (i : \operatorname{Fin}\left(k\right)), \operatorname{rotor}\left(B, theta, i\right) = ((\operatorname{algebraMap}\left(\mathbb{R}, \operatorname{CliffordAlgebra}\left(q\right), \operatorname{c}\left(theta, i\right)\right)) + ((\operatorname{s}\left(theta, i\right)) \cdot (B\left(i\right))))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.rotor` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.3, page 9: “Let B ∈ C be a bivector with B² = −1 and θ ∈ ℝ. Then U(θ) = exp((θ/2)B) = cos(θ/2) + B sin(θ/2) is called the rotor generated by B with parameter θ.” Scalars enter by algebraMap and scalar multiplication.

**Definition 1.11 (Ordered rotor chain).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \operatorname{chain}\left(B, theta\right) = (((\operatorname{List}.\operatorname{finRange}\left(k\right)).\operatorname{map}\left(\operatorname{rotor}\left(B, theta\right)\right)).\operatorname{prod})$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.chain` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Section 1.1, page 3: “We consider the ordered chain Pₖ = U₁U₂⋯Uₖ”. List.finRange preserves the source order.

**Definition 1.12 (Permuted reversed factors).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{returnProduct}\left(B, theta, tau\right) = (((\operatorname{List}.\operatorname{finRange}\left(k\right)).\operatorname{map}\left((\operatorname{fun} j \mapsto \operatorname{CliffordAlgebra}.\operatorname{reverse}\left(\operatorname{rotor}\left(B, theta, tau\left(j\right)\right)\right))\right)).\operatorname{prod})$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.returnProduct` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D5.2, page 18: “Let τ be a permutation of {1, …, k}. We set Qₖ⁽τ⁾ = Ũτ₍₁₎ Ũτ₍₂₎ ⋯ Ũτ₍ₖ₎, Θₖ(τ) = PₖQₖ⁽τ⁾”. CliffordAlgebra.reverse is the native reversion.

**Definition 1.13 (Permuted rotor loop).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{loop}\left(B, theta, tau\right) = ((\operatorname{chain}\left(B, theta\right)) \cdot (\operatorname{returnProduct}\left(B, theta, tau\right)))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.loop` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D5.2, page 18: “Θₖ(τ) = PₖQₖ⁽τ⁾”. Both factors are ordered native Clifford products.

**Definition 1.14 (Restricted inversions).**

$$\forall (k : \mathbb{N}), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{inversionCount}\left(tau, S\right) = (((\operatorname{Finset}.\operatorname{product}\left(S, S\right)).\operatorname{filter}\left((\operatorname{fun} p \mapsto ((p).\operatorname{fst} < ((p).\operatorname{snd})) \land ((tau).\operatorname{symm}\left((p).\operatorname{snd}\right) < ((tau).\operatorname{symm}\left((p).\operatorname{fst}\right))))\right)).\operatorname{card})$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.inversionCount` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D5.2, page 18: “For S ⊆ {1, …, k} let ι(τ, S) := #{(i, j) ∈ S × S : i < j, τ⁻¹(i) > τ⁻¹(j)} be the inversion count of τ on S.” Each ordered pair is counted once.

**Definition 1.15 (Period-four sign).**

$$\forall (m : \mathbb{N}), \operatorname{eta}\left(m\right) = ((((-(1) : \mathbb{R}))^{m}) \cdot (((-(1) : \mathbb{R}))^{\operatorname{Nat}.\operatorname{div}\left((m) \cdot ((m) + (1)), 2\right)}))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.eta` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D5.1, page 16: “We set for m ∈ ℕ₀ η(m) := (−1)ᵐ · (−1)ᵐ⁽ᵐ⁺¹⁾⁄² = (−1)ᵐ⁽ᵐ⁺³⁾⁄².” Nat.div is natural-number division.

**Definition 1.16 (The formula without the star condition).**

$$\operatorname{claim} = (\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), ((q).\operatorname{Nondegenerate}) \Rightarrow (\forall (k : \mathbb{N}), (1 \le (k)) \Rightarrow (\forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), (\operatorname{AnticommutingUnitFamily}\left(q, k, B\right)) \Rightarrow (\forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{scalarProjection}\left(q, \operatorname{loop}\left(B, theta, tau\right)\right) = (\sum_{S \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} ((((\operatorname{eta}\left((S).\operatorname{card}\right)) \cdot (((-(1) : \mathbb{R}))^{\operatorname{inversionCount}\left(tau, S\right)})) \cdot (\prod_{i \in S} (\operatorname{w}\left(theta, i\right)))) \cdot (\prod_{i \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)} ((1) - (\operatorname{w}\left(theta, i\right))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.claim` (`✓ std3`).

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Remark 5.7 in the TeX, rendered Remark 5.5, page 19: “The hypotheses of Theorem 5.5 can be sharpened at two points. First, for τ = id no star condition is needed: that is Theorem 5.2, whose pairing argument cancels the odd off-diagonal terms in pairs. Second, this pairing argument fails termwise for τ ≠ id. Nevertheless, numerical evidence suggests that the formula also holds without the star condition in that case: tested on the triangle family from Remark 4.4, which violates the star condition, under all six permutations of {1, 2, 3} with random parameter sets; the largest deviation encountered was in the range of double machine precision. A general proof would have to capture the cancellation of the odd off-diagonal terms in coarser groups than pairs; we have not determined such a grouping.” The form is real, finite-dimensional and nondegenerate; k is positive. Fin k relabels the source indices increasingly. Every angle and permutation is quantified; the star condition is absent.

**Theorem 1.17 (Cyclicity of the native scalar coefficient).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (x : \operatorname{CliffordAlgebra}\left(q\right)), \forall (y : \operatorname{CliffordAlgebra}\left(q\right)), \operatorname{scalarProjection}\left(q, (x) \cdot (y)\right) = (\operatorname{scalarProjection}\left(q, (y) \cdot (x)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.scalar_cyclic` (`✓ std3`). ∎

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Lemma 2.1 in the TeX, rendered Lemma 2.3, page 8: “For all x, y ∈ C, ⟨xy⟩₀ = ⟨yx⟩₀.” The native contraction proof also applies to degenerate forms and spaces of arbitrary dimension.

**Theorem 1.18 (Reversion of a bivector rotor).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), \forall (k : \mathbb{N}), \forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), (\forall (i : \operatorname{Fin}\left(k\right)), \operatorname{IsBivector}\left(q, B\left(i\right)\right)) \Rightarrow (\forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (i : \operatorname{Fin}\left(k\right)), \operatorname{CliffordAlgebra}.\operatorname{reverse}\left(\operatorname{rotor}\left(B, theta, i\right)\right) = ((\operatorname{algebraMap}\left(\mathbb{R}, \operatorname{CliffordAlgebra}\left(q\right), \operatorname{c}\left(theta, i\right)\right)) - ((\operatorname{s}\left(theta, i\right)) \cdot (B\left(i\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.reverse_rotor` (`✓ std3`). ∎

*Citation.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Definition D2.3, page 9: “We have Ũ(θ) = cos(θ/2) − B sin(θ/2) = U(−θ)”. Homogeneous degree two suffices; the square condition is unnecessary for this identity.

**Theorem 1.19 (Squares of subset coefficients).**

$$\forall (k : \mathbb{N}), \forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), (\operatorname{a}\left(theta, S\right))^{2} = ((\prod_{i \in S} (\operatorname{w}\left(theta, i\right))) \cdot (\prod_{i \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)} ((1) - (\operatorname{w}\left(theta, i\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.coefficient_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Squaring the subset coefficient replaces sine factors by w and cosine factors by 1 − w. This remains valid when either trigonometric factor vanishes.

**Theorem 1.20 (Scalar support of an anticommuting family).**

$$\forall (A : Type*), [\operatorname{Ring}\left(A\right)] [\operatorname{Algebra}\left(\mathbb{R}, A\right)] \forall (k : \mathbb{N}), \forall (t : \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right)), (\forall (x : A), \forall (y : A), t\left((x) \cdot (y)\right) = (t\left((y) \cdot (x)\right))) \Rightarrow (\forall (B : (\operatorname{Fin}\left(k\right) \to A)), (\forall (i : \operatorname{Fin}\left(k\right)), (B\left(i\right)) \cdot (B\left(i\right)) = (-(1))) \Rightarrow ((\forall (i : \operatorname{Fin}\left(k\right)), \forall (j : \operatorname{Fin}\left(k\right)), (i \ne (j)) \Rightarrow ((B\left(i\right)) \cdot (B\left(j\right)) = (-((B\left(j\right)) \cdot (B\left(i\right)))))) \Rightarrow (\forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), ((S).\operatorname{Nonempty}) \Rightarrow ((\neg ((S = ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)))) \land (\operatorname{Odd}\left(k\right)))) \Rightarrow (t\left((((S).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod}\right) = (0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.tracial_subset_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

A nonempty ordered product has zero value under a real linear tracial functional, except possibly when its support is full and the family size is odd. An anticommuting conjugation changes the sign in every other case.

**Theorem 1.21 (Off-diagonal scalar products vanish).**

$$\forall (A : Type*), [\operatorname{Ring}\left(A\right)] [\operatorname{Algebra}\left(\mathbb{R}, A\right)] \forall (k : \mathbb{N}), \forall (t : \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right)), (\forall (x : A), \forall (y : A), t\left((x) \cdot (y)\right) = (t\left((y) \cdot (x)\right))) \Rightarrow (\forall (B : (\operatorname{Fin}\left(k\right) \to A)), (\forall (i : \operatorname{Fin}\left(k\right)), (B\left(i\right)) \cdot (B\left(i\right)) = (-(1))) \Rightarrow ((\forall (i : \operatorname{Fin}\left(k\right)), \forall (j : \operatorname{Fin}\left(k\right)), (i \ne (j)) \Rightarrow ((B\left(i\right)) \cdot (B\left(j\right)) = (-((B\left(j\right)) \cdot (B\left(i\right)))))) \Rightarrow (\forall (S : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), \forall (T : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), (S \ne (T)) \Rightarrow ((\neg ((\operatorname{Odd}\left(k\right)) \land (T = (((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S))))) \Rightarrow (t\left(((((S).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod}) \cdot ((((T).\operatorname{sort}\left((\operatorname{fun} u \mapsto (\operatorname{fun} v \mapsto u \le (v)))\right)).\operatorname{map}\left(B\right)).\operatorname{prod})\right) = (0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.tracial_off_diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Two different subset products have zero tracial pairing unless the family size is odd and their supports are complementary. The statement makes no independence assumption.

**Theorem 1.22 (Square of an ordered anticommuting product).**

$$\forall (A : Type*), [\operatorname{Ring}\left(A\right)] [\operatorname{Algebra}\left(\mathbb{R}, A\right)] \forall (I : Type*), \forall (B : (I \to A)), (\forall (i : I), (B\left(i\right)) \cdot (B\left(i\right)) = (-(1))) \Rightarrow ((\forall (i : I), \forall (j : I), (i \ne (j)) \Rightarrow ((B\left(i\right)) \cdot (B\left(j\right)) = (-((B\left(j\right)) \cdot (B\left(i\right)))))) \Rightarrow (\forall (l : \operatorname{List}\left(I\right)), ((l).\operatorname{Nodup}) \Rightarrow ((((l).\operatorname{map}\left(B\right)).\operatorname{prod}) \cdot (((l).\operatorname{map}\left(B\right)).\operatorname{prod}) = ((((-(1) : \mathbb{R}))^{\operatorname{Nat}.\operatorname{choose}\left(((l).\operatorname{length}) + (1), 2\right)}) \cdot ((1 : A))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.anticommuting_list_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

A product of distinct anticommuting elements squaring to −1 has square (−1) to the triangular exponent. The order is arbitrary and the carrier is any real algebra.

## References

- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.AnticommutingUnitFamily`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.IsBivector`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.StarCondition`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.a`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.anticommuting_list_square`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.c`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.chain`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.claim`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.coefficient_square`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.eta`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.inversionCount`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.loop`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.returnProduct`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.reverse_rotor`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.rotor`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.s`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.scalarProjection`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.scalar_cyclic`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.subsetProduct`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.tracial_off_diagonal_zero`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.tracial_subset_vanishing`
- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.w`
