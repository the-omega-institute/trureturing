# Symmetric SATWAP attainment in every dimension

## Abstract

Identical TW measurements attain the symmetric SATWAP value 2(d−1) on a swap-invariant maximally entangled vector in every dimension d at least two.

Fin d indexes the computational basis from zero to d−1. Both parties use the same measurement function. Settings zero and one below correspond respectively to settings one and two in the symmetric SATWAP expression. Nat.cast carries a natural number to its displayed target type, Complex.ofReal includes a real scalar in the complex numbers, and Fin.val extracts a natural index. WithLp.ofLp and WithLp.toLp change between the Euclidean vector and its coordinate function.

**Definition 1.1 (Real powers of the root of unity).**

$$\forall (d: \mathbb{N}), (\forall (t: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.omegaPow}\left(d, t\right): \mathbb{C}) = \operatorname{Complex.exp}\left(\frac{2 \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.pi}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{Complex.ofReal}\left(t\right)}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.omegaPow` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

The phase is the complex exponential with real exponent t. It extends the root of unity in the source's TeX lines 519–520 to the fractional exponents used in line 530. The definition is total also at dimension zero, using division in the complex field.

**Definition 1.2 (The TW change of measurement basis).**

$$\forall (d: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.twMatrix}\left(d\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = \operatorname{Matrix.diagonal}\left(\lambda (i: \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{ite}\left((\operatorname{Fin.val}\left(i\right) = (0: \mathbb{N})), -(1: \mathbb{C}), (1: \mathbb{C})\right))\right) \cdot \operatorname{Matrix.of}\left(\lambda (i: \operatorname{Fin}\left(d\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(d\right)) \mapsto (\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C}) \cdot \operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\left((\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(i\right)\right): \mathbb{R}) - (\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(j\right)\right): \mathbb{R}) - \frac{(1: \mathbb{R})}{2}\right) \cdot \operatorname{Real.pi}}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})}\right)\right)}))\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.twMatrix` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

The diagonal factor T has first entry −1 and every other entry 1. The second factor W has the reciprocal sine entries of Eq. (TW), TeX lines 488–495. Their product is the source's U=TW. The sine is evaluated over the reals and then included in the complex denominator; each row and column index is first extracted from Fin d and cast to a real number.

**Definition 1.3 (Identical measurements for the two parties).**

$$\forall (d: \mathbb{N}), (\forall (x: \operatorname{Fin}\left(2\right)), (\forall (a: \operatorname{Fin}\left(d\right)), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.measurement}\left(d, x, a\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = \operatorname{ite}\left((x = (0: \operatorname{Fin}\left(2\right))), \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector}\left(a\right), \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.twMatrix}\left(d\right) \cdot \operatorname{D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector}\left(a\right) \cdot \operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.twMatrix}\left(d\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.measurement` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

Setting zero uses the computational basis projector at outcome a. Setting one conjugates that projector by TW. These are the two measurements of Eq. (CGLMP-Opt), TeX lines 488–497; the same matrices are used at either party.

**Definition 1.4 (The Born quadratic form).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\forall (x: \operatorname{Fin}\left(2\right)), (\forall (y: \operatorname{Fin}\left(2\right)), (\forall (a: \operatorname{Fin}\left(d\right)), (\forall (b: \operatorname{Fin}\left(d\right)), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.prob}\left(d, \psi, x, y, a, b\right): \mathbb{C}) = \operatorname{Inner.inner}\left(\mathbb{C}, \psi, \operatorname{WithLp.toLp}\left(2, \operatorname{Matrix.mulVec}\left(\operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto (x1 \cdot x2)), \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.measurement}\left(d, x, a\right), \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.measurement}\left(d, y, b\right)\right), \operatorname{WithLp.ofLp}\left(\psi\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.prob` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

Apply the tensor product of the two outcome operators to the coordinate function of ψ, return to Euclidean space, and take its inner product with ψ. This is the pure-vector form of Born's rule in Eq. (Born), TeX lines 179–189. The function is complex-valued and is defined for every vector, without a normalization assumption.

**Definition 1.5 (The equal negative-power correlator).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), (\forall (x: \operatorname{Fin}\left(2\right)), (\forall (y: \operatorname{Fin}\left(2\right)), (\forall (k: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.correlator}\left(d, \psi, x, y, k\right): \mathbb{C}) = \sum_{(a: \operatorname{Fin}\left(d\right))} (\sum_{(b: \operatorname{Fin}\left(d\right))} (\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.omegaPow}\left(d, -\left((\operatorname{Nat.cast}\left(k\right): \mathbb{R}) \cdot \left((\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(a\right)\right): \mathbb{R}) + (\operatorname{Nat.cast}\left(\operatorname{Fin.val}\left(b\right)\right): \mathbb{R})\right)\right)\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.prob}\left(d, \psi, x, y, a, b\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.correlator` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

Sum the outcome quadratic forms with phase ω raised to −k(a+b). This is the case with both exponents equal to −k in Eq. (Correlators:d), TeX lines 513–520. The natural index k and the two natural outcome values are cast to the reals before forming the phase exponent.

**Definition 1.6 (The symmetric SATWAP expression).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.satwapValue}\left(d, \psi\right): \mathbb{C}) = \sum_{(k: \mathbb{N}) \in \operatorname{Finset.Icc}\left((1: \mathbb{N}), \operatorname{Nat.sub}\left(d, 1\right)\right)} (\operatorname{let} (a: \mathbb{C}) = \frac{(1: \mathbb{C}) - \operatorname{Complex.I}}{2} \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.omegaPow}\left(d, \frac{(\operatorname{Nat.cast}\left(k\right): \mathbb{R})}{4}\right); (\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.omegaPow}\left(d, -(2: \mathbb{R}) \cdot (\operatorname{Nat.cast}\left(k\right): \mathbb{R})\right) \cdot \left(a \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.correlator}\left(d, \psi, (0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)), k\right) + \operatorname{starRingEnd}\left(\mathbb{C}\right)\left(a\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.correlator}\left(d, \psi, (0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)), k\right) + \operatorname{starRingEnd}\left(\mathbb{C}\right)\left(a\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.correlator}\left(d, \psi, (1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)), k\right)\right) + \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.omegaPow}\left(d, -(3: \mathbb{R}) \cdot (\operatorname{Nat.cast}\left(k\right): \mathbb{R})\right) \cdot a \cdot \operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.correlator}\left(d, \psi, (1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)), k\right)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.satwapValue` (`✓ std3`).

*Citation.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

The finite sum and the complex coefficient a reproduce Eq. (symSATWAP), TeX lines 523–530, with the stated change of setting labels. The first three correlators carry the phase ω raised to −2k; the last carries ω raised to −3k. The coefficient is (1−i)ω raised to k/4, divided by two, and starRingEnd is complex conjugation. Nat.sub is truncated natural subtraction, so the interval is empty when d is zero or one.

**Definition 1.7 (The reduced rank-one operator).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.reducedState}\left(\psi\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\operatorname{WithLp.ofLp}\left(\psi\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.reducedState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

Form the rank-one operator of the coordinate function of ψ and trace out its second factor. The resulting d by d matrix is the first party's reduced operator. For a unit vector it is a density matrix.

**Definition 1.8 (Attainment with a symmetric maximally entangled vector).**

$$(\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \to (\exists (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), ((\left\lVert \psi \right\rVert = (1: \mathbb{R})) \land ((\operatorname{LinearIsometryEquiv.piLpCongrLeft}\left(2, \mathbb{C}, \mathbb{C}, \operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \psi\right) = \psi) \land ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.reducedState}\left(\psi\right) = (\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))) \land (\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.satwapValue}\left(d, \psi\right) = (2: \mathbb{C}) \cdot \left((\operatorname{Nat.cast}\left(d\right): \mathbb{C}) - (1: \mathbb{C})\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

For every natural dimension d at least two, one Euclidean vector ψ has norm one, is fixed by exchanging its two indices, has reduced operator equal to the identity divided by d, and gives the complex SATWAP value 2(d−1). This is the attainment question in the source's TeX line 532, with symmetry as in lines 285–297. The reduced-operator identity expresses maximal entanglement of the pure vector.

**Theorem 1.9 (Attainment for every dimension at least two).**

$$\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \to (\exists (\psi: \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), ((\left\lVert \psi \right\rVert = (1: \mathbb{R})) \land ((\operatorname{LinearIsometryEquiv.piLpCongrLeft}\left(2, \mathbb{C}, \mathbb{C}, \operatorname{Equiv.prodComm}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \psi\right) = \psi) \land ((\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.reducedState}\left(\psi\right) = (\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))) \land (\operatorname{D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.satwapValue}\left(d, \psi\right) = (2: \mathbb{C}) \cdot \left((\operatorname{Nat.cast}\left(d\right): \mathbb{C}) - (1: \mathbb{C})\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hsu-et-al-2026-symmetric-satwap-maximal-violation` (proved) by `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hsu-et-al-2026-symmetric-satwap-maximal-violation","declaration_gid":"D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hsin-Yu Hsu; Gelo Noel M. Tabia; Kai-Siang Chen; Mu-En Liu; Tamás Vértesi; Nicolas Brunner; Yeong-Cherng Liang (2026). *Trading symmetry for Hilbert-space dimension in Bell-inequality violation*. DOI: [10.1088/2058-9565/ae6bb1](https://doi.org/10.1088/2058-9565/ae6bb1). URL: <https://arxiv.org/abs/2601.02893v4>.

*Commentary.*

Fix d at least two and write ωᵗ for omegaPow d t. Multiplication adds phase exponents, conjugation negates them, and ω⁰=1. Put α₀=7/8 and α₁=11/8, and let Vₓ have entries ω raised to j(a+αₓ), divided by √d. In Vₓ†Vₓ the offsets cancel. Orthogonality of the finite exponential sum gives d on the diagonal and zero elsewhere, so Vₓ†Vₓ=I.

Let D be diagonal with entries ω raised to a/2 and F diagonal with entries −i times ω raised to −(b+1/2)/2. For δ=b−a+1/2 the phase q=ωᵟ satisfies qᵈ=−1, hence q≠1. The geometric sum is therefore −2/(q−1). With θ=(a−b−1/2)π/d, the exponential formula for sine rewrites this as −iω raised to −δ/2, divided by sin θ. The same identity and the nonzero exponential show sin θ≠0. Entrywise multiplication now gives V₀†V₁=DWF.

The diagonal matrices D and T are unitary. Thus L=TD†V₀† is unitary and LL†=I. Define ψ at the pair (i,j) to be the sum over m of LᵢₘLⱼₘ, divided by √d. Its coefficient matrix is A=LLᵀ/√d. The matrix LLᵀ is symmetric, so exchanging i and j fixes ψ. Since L and its transpose are unitary, the reduced rank-one operator is AA†=I/d. Taking the trace identifies the squared norm of ψ with one; nonnegativity of the norm gives norm one.

Let B₀=I and B₁=TW be the matrices of measurement columns. The diagonal entries of D and F have modulus one, as do all phases ωᵗ. Each outcome operator is consequently the rank-one operator of its column in Bₓ. For G₀=TD† and G₁=F the identities LV₀=B₀G₀ and LV₁=B₁G₁ follow respectively from V₀†V₀=I and V₀†V₁=DWF. Both Gₓ are diagonal unitary, and these identities imply Bₓ†L=GₓVₓ†.

The tensor product of the two rank-one outcome operators is again rank one. Its quadratic form is the squared modulus of the overlap with ψ. Writing Q=LLᵀ, that overlap is the (a,b) entry of Bₓ†Q(Bᵧ†)ᵀ, divided by √d. The preceding identities turn this matrix into Gₓ[Vₓ†(Vᵧ†)ᵀ]Gᵧ. Its diagonal phases disappear on taking the norm. Thus, with s=αₓ+αᵧ, the outcome value is d⁻³ times the squared modulus of the sum over j of ω raised to −j(a+b+s).

For an integer n, the sum over a from zero to d−1 of ω raised to an is d when d divides n and zero otherwise. Identify Fin d with ZMod d, express the summands using its standard additive character, and apply character orthogonality. Next fix 0≤k<d. For each l, the divisibility condition d divides j−l−k selects exactly j=l+k if l+k<d, and j=l+k−d otherwise. There are d−k indices in the first case and k in the second. The corresponding double sum of ω raised to (j−l)s is (d−k)ω raised to ks plus k times ω raised to (k−d)s.

Expand the squared modulus in the outcome value into a sum over j and l, multiply by the correlator phase, and interchange the finite sums. The two sums over outcomes vanish unless d divides j−l−k; when it does, each contributes d. For 1≤k≤d−1 the preceding count therefore gives the correlator as ω raised to ks, multiplied by [(d−k)+kω raised to −ds]/d. The three possible values of s are 7/4, 9/4 and 11/4. Periodicity of the complex exponential gives ω raised to −ds equal to i, −i and i respectively.

Substitute these correlators into each summand of satwapValue. The phases cancel because −2k+k/4+7k/4=0, −2k−k/4+9k/4=0 and −3k+k/4+11k/4=0. The two equal-setting terms each have coefficient (1−i)/2 and numerator d−k+ki; the two mixed-setting terms together have coefficient 1+i and numerator d−k−ki. Dividing by d and using i²=−1 gives exactly two. The interval from one to d−1 has d−1 elements, so its sum is 2(d−1). The vector ψ thus satisfies all four required identities.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.correlator`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.measurement`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.omegaPow`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.prob`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.reducedState`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.satwapValue`
- Truth anchor: `D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.twMatrix`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration](../../ConceptDynamics/Coding/CountedOriginalOrbitGyration.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](../Measurement/OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate](../Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
