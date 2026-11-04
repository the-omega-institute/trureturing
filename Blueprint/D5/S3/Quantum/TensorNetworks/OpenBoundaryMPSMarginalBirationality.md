# Rational reconstruction from three consecutive sites

## Abstract

Every three-site improper marginal of an open-boundary binary bond-two matrix product state has a rational inverse on a nonempty Zariski-open subset.

**Definition 1.1 (Open-boundary amplitudes).**

$$\forall (n: \mathbb{N}), (\forall (a_{0}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b_{0}: (\operatorname{Fin}\left(2\right)) \to (\mathbb{C})), (\forall (b_{1}: (\operatorname{Fin}\left(2\right)) \to (\mathbb{C})), (\operatorname{mpsState}\left(n, a_{0}, a_{1}, b_{0}, b_{1}\right) = (\lambda (w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{dotProduct}\left(b_{0}, \operatorname{Matrix.mulVec}\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto ((![a_{0}, a_{1}]: (\operatorname{Fin}\left(2\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))\left(w\left(j\right)\right)))\right)\right), b_{1}\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.mpsState` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The amplitude of the word w is b₀ᵀA[w(0)]⋯A[w(n−1)]b₁, with A₀ = a₀ and A₁ = a₁. The matrices are the same at every site, and the two boundary vectors are independent. The dot product is bilinear over the complex numbers, without conjugation. The list product preserves the site order and is the identity matrix when n is zero. This is equation (eqn-phi2) of the source, sigma14-095.tex, lines 349–358, specialized to physical and bond dimensions two.

**Definition 1.2 (The parametrized model).**

$$\forall (n: \mathbb{N}), (\operatorname{openBoundaryMPS}\left(n\right) = \{(\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})) \mid (\exists (a_{0}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b_{0}: (\operatorname{Fin}\left(2\right)) \to (\mathbb{C})), (\exists (b_{1}: (\operatorname{Fin}\left(2\right)) \to (\mathbb{C})), (\psi = \operatorname{mpsState}\left(n, a_{0}, a_{1}, b_{0}, b_{1}\right))))))\})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.openBoundaryMPS` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The model consists of all amplitude functions obtained by varying the two complex two-by-two matrices and both complex boundary vectors. It is OB(2,2,n) in the source, sigma14-095.tex, lines 360–363.

**Definition 1.3 (The vanishing ideal).**

$$\forall (n: \mathbb{N}), (\operatorname{vanishingPolys}\left(n\right) = \operatorname{MvPolynomial.vanishingIdeal}\left(\mathbb{C}, \operatorname{openBoundaryMPS}\left(n\right)\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.vanishingPolys` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

These are all complex polynomials in the word coordinates that vanish on every state in the parametrized model. They are the equations used to take the Zariski closure of OB(2,2,n), as in sigma14-095.tex, lines 360–363.

**Definition 1.4 (The affine Zariski closure).**

$$\forall (n: \mathbb{N}), (\operatorname{closure}\left(n\right) = \operatorname{MvPolynomial.zeroLocus}\left(\mathbb{C}, \operatorname{vanishingPolys}\left(n\right)\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.closure` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The closure is the common zero set of the vanishing ideal of the parametrized model. Thus it is the affine Zariski closure, denoted by the closure of OB(2,2,n) in the source, sigma14-095.tex, lines 360–363.

**Definition 1.5 (Summing outside a consecutive triple).**

$$\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), (\forall (h: a + 3 \le n), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), (\operatorname{improperMarginal}\left(n, a, h, \psi\right) = (\lambda (t: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\sum_{(w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)))} (\operatorname{ite}\left((\lambda (j: \operatorname{Fin}\left(3\right)) \mapsto (w\left((\operatorname{Fin.mk}\left(a + (\operatorname{Fin.val}\left(j\right): \mathbb{N})\right): \operatorname{Fin}\left(n\right))\right))) = t, \psi\left(w\right), (0: \mathbb{C})\right))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.improperMarginal` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each three-letter word t, sum the amplitudes of all n-letter words whose letters at positions a, a+1 and a+2 equal t. This sums every index outside the three consecutive sites, as in sigma14-095.tex, lines 420–426. The sum is coherent in complex amplitudes. The bound a+3 ≤ n makes each selected index valid; Fin.val is the inclusion of a finite index into the natural numbers. The proof h of the indexing bound is an explicit argument.

**Definition 1.6 (A rational inverse on principal open subsets).**

$$\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), (\forall (h: a + 3 \le n), (\operatorname{IsBirationalVia}\left(n, a, h\right) = (\exists (g: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\exists (q: \operatorname{MvPolynomial}\left((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\exists (p: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\operatorname{MvPolynomial}\left((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right))), ((\exists (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\psi \in \operatorname{closure}\left(n\right)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, \psi\right), g\right) \ne (0: \mathbb{C})))) \land ((\forall (t: ((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((t \in \operatorname{closure}\left(3\right)) \Rightarrow ((\operatorname{MvPolynomial.eval}\left(t, g\right) \ne (0: \mathbb{C})) \Rightarrow ((\operatorname{MvPolynomial.eval}\left(t, q\right) \ne (0: \mathbb{C})) \land (((\lambda (w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\frac{\operatorname{MvPolynomial.eval}\left(t, p\left(w\right)\right)}{\operatorname{MvPolynomial.eval}\left(t, q\right)})) \in \operatorname{closure}\left(n\right)) \land ((\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, (\lambda (w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\frac{\operatorname{MvPolynomial.eval}\left(t, p\left(w\right)\right)}{\operatorname{MvPolynomial.eval}\left(t, q\right)}))\right), g\right) \ne (0: \mathbb{C})) \land (\operatorname{improperMarginal}\left(n, a, h, (\lambda (w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\frac{\operatorname{MvPolynomial.eval}\left(t, p\left(w\right)\right)}{\operatorname{MvPolynomial.eval}\left(t, q\right)}))\right) = t))))))) \land (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (\mathbb{C})), ((\psi \in \operatorname{closure}\left(n\right)) \Rightarrow ((\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, \psi\right), g\right) \ne (0: \mathbb{C})) \Rightarrow ((\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, \psi\right), q\right) \ne (0: \mathbb{C})) \land ((\lambda (w: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\frac{\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, \psi\right), p\left(w\right)\right)}{\operatorname{MvPolynomial.eval}\left(\operatorname{improperMarginal}\left(n, a, h, \psi\right), q\right)})) = \psi)))))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.IsBirationalVia` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The polynomials g and q and the coordinate polynomials p give the rational map F(t)(w) = p(w)(t)/q(t). The three conjuncts say respectively that the source chart is nonempty, that F maps the target chart into the source chart and is a right inverse there, and that F is a left inverse on the source chart, with the denominator nonzero on both charts. Write Xₙ for the affine closure. Since the linear marginal takes the parametrized models into one another, it also takes their Zariski closures into one another. Consequently these conditions express the isomorphism between the nonempty Zariski-open subsets U = {ψ ∈ Xₙ : g(mψ) ≠ 0} and V = {t ∈ X₃ : g(t) ≠ 0}, given by the marginal and its rational inverse. For irreducible Xₙ and X₃ these subsets are dense. The proof h of the indexing bound is an explicit argument.

**Definition 1.7 (The three-site birationality conjecture).**

$$\operatorname{claim} = (\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), ((4 \le n) \Rightarrow (\forall (h: a + 3 \le n), ((\operatorname{Ideal.IsPrime}\left(\operatorname{vanishingPolys}\left(n\right)\right)) \land ((\operatorname{Ideal.IsPrime}\left(\operatorname{vanishingPolys}\left(3\right)\right)) \land (\operatorname{IsBirationalVia}\left(n, a, h\right))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.claim` (`✓ std3`).

*Citation.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural n at least four and every starting position a with a+3 ≤ n, the two vanishing ideals are prime and the improper marginal has the rational inverse described by the three clauses. This states Conjecture 8, sigma14-095.tex, lines 430–434, with birational equivalence expressed by rational maps on nonempty principal open subsets.

**Theorem 1.8 (Birationality of every consecutive three-site marginal).**

$$\forall (n: \mathbb{N}), (\forall (a: \mathbb{N}), ((4 \le n) \Rightarrow (\forall (h: a + 3 \le n), ((\operatorname{Ideal.IsPrime}\left(\operatorname{vanishingPolys}\left(n\right)\right)) \land ((\operatorname{Ideal.IsPrime}\left(\operatorname{vanishingPolys}\left(3\right)\right)) \land (\operatorname{IsBirationalVia}\left(n, a, h\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.result` (`✓ std3`). ∎

*Resolves.* `Problems/critch-morton-2014-open-boundary-mps-marginal-birationality` (proved) by `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"critch-morton-2014-open-boundary-mps-marginal-birationality","declaration_gid":"D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

First express each word amplitude as a polynomial in the twelve matrix and boundary entries. Substitution into these polynomials is a homomorphism from the coordinate polynomial ring to the parameter polynomial ring. Its kernel equals the vanishing ideal: evaluation on all complex parameter values detects a zero polynomial. The parameter polynomial ring is an integral domain, so this kernel is prime. This applies to every length, in particular n and three.

For a three-site tensor t, let Tⱼ have entries t(i,j,k), and form the four-by-four matrix K(t) whose row (i,k) is (t(i,k,0), t(i,k,1), −t(0,i,k), −t(1,i,k)). Its determinant is a quartic vanishing on the three-site model. To see this as a polynomial identity, let U have rows b₀ᵀAᵢ and W have columns Aₖb₁. The vectors z = det(U) adj(W)b₁ and e = det(W)b₀ᵀadj(U) satisfy K(t)(z₀,z₁,e₀,e₁)ᵀ = 0. The component e₀ is a nonzero parameter polynomial, as is seen with A₀ the identity, A₁ the exchange matrix and both boundaries (1,0). The determinant therefore vanishes identically in the parameter domain. It belongs to the vanishing ideal, so det K(t) = 0 on X₃ as well. The source's three-site quartic hypersurface is described in sigma14-095.tex, lines 378–406.

Let d be the determinant of the leading three-by-three minor of K, and let Δ₀, Δ₁, Δ₂ be its Cramer determinants for minus the first three entries of the last column of K. The polynomial identity K(Δ₀,Δ₁,Δ₂,d)ᵀ = (0,0,0,det K)ᵀ gives, when d ≠ 0, a kernel vector (z₀,z₁,ℓ₀,1) with z = (Δ₀,Δ₁)/d and ℓ = (Δ₂,d)/d. The nonzero minor also makes every kernel vector proportional to this one. Put Vᵢₖ = (ℓTᵢ)ₖ, Bⱼ = TⱼV⁻¹, r = Vz and C = B₀+B₁. For the polynomial chart, put L = (Δ₂,d), Z = (Δ₀,Δ₁), Wᵢₖ = (LTᵢ)ₖ, Hⱼ = Tⱼadj(W), H = H₀+H₁ and R = WZ; thus W = dV on d ≠ 0. Take g to be d det(W) det(H) times the two minors t(0,0,0)t(1,0,1)−t(0,0,1)t(1,0,0) and t(0,0,0)t(0,1,1)−t(0,0,1)t(0,1,0). On g ≠ 0 both V and C are invertible. The kernel equations give Tₖz = Veₖ, while the definition of V gives ℓBᵢ = eᵢᵀ. It follows that Bₖr = Veₖ and ℓBᵢBⱼBₖr = t(i,j,k). Thus the reconstructed parameters reproduce t.

For b = n−3−a, define Fₙ,ₐ(t)(w) = ℓ(C⁻¹)ᵃB[w(0)]⋯B[w(n−1)](C⁻¹)ᵇr. This is a rational map with common denominator q = det(W)³ det(H)ⁿ⁻³ and coordinate numerator p(w) = L adj(H)ᵃH[w(0)]⋯H[w(n−1)]adj(H)ᵇR. Indeed Bⱼ = (d/det W)Hⱼ, ℓ = L/d, r = R/d² and C⁻¹ = (det W/(d det H))adj(H); substituting these expressions and using n = a+b+3 gives exactly p(w)/q. The chart makes q nonzero. The expression for F is an n-site state with matrices B₀,B₁ and boundaries ℓ(C⁻¹)ᵃ and (C⁻¹)ᵇr, so it lies in the model and hence in Xₙ. Splitting a word into its prefix, middle triple and suffix shows that summing all length-k outside words replaces their matrix products by Cᵏ. The outside sums therefore cancel the inverse powers on both sides, leaving the reconstructed triple t. Hence mF(t) = t, and g(mF(t)) = g(t) ≠ 0.

For uniqueness first take an actual n-site state with matrices A₀,A₁ and boundaries α,β. Write S = A₀+A₁, l = αᵀSᵃ and r′ = Sᵇβ for its marginal boundaries. Let U have rows lAᵢ and W have columns Aₖr′. The nonzero endpoint minor of the triple makes both U and W invertible, since T₀ = UA₀W. The vector (W⁻¹r′, lU⁻¹) is in the kernel of K. Its last component s is nonzero: otherwise kernel uniqueness makes the whole vector zero, contradicting invertibility of W. Comparison with the normalized Cramer vector gives ℓ = s⁻¹lU⁻¹, Bⱼ = sUAⱼU⁻¹ and r = s⁻²Ur′. In particular C = sUSU⁻¹. Conjugation cancels throughout the word product, and the total scalar in F is sⁿs⁻¹s⁻ᵃs⁻ᵇs⁻² = 1 because n = a+b+3. Thus F(mψ) = ψ on the parametrized model wherever g(mψ) ≠ 0.

Extend this equality to Xₙ coordinate by coordinate. Pull back g, q and p(w) along the linear marginal. The polynomial (g∘m)((p(w)∘m)−ψ(w)(q∘m)) vanishes on the model: when g(mψ) is zero the first factor vanishes, and otherwise uniqueness and the nonzero denominator make the second factor vanish. It therefore vanishes on Xₙ. On the chart, cancel g(mψ) and divide by q(mψ), obtaining F(mψ) = ψ on the closure.

Finally there exists a triple t in X₃ with g(t) ≠ 0. To prove this, choose A₀ = ((1,2),(3,4)), A₁ = ((5,6),(7,8)), b₀ = (1,0) and b₁ = (1,2). The resulting triple, in lexicographic word order, is (145,349,337,829,489,1173,1193,2933). At this point d = 387072 and (Δ₀,Δ₁,Δ₂) = (118272,10752,−1161216); the reconstructed determinants are det V = 1152 and det C = −2, and the two endpoint minors are −576 and 2592. Every factor of g is nonzero. Thus the target chart contains a point t, and Fₙ,ₐ sends any such point to a point of Xₙ whose marginal is t. The existence of t supplies the nonempty source chart for every n, a and bound proof h in the stated range. Together with primeness and the two inverse identities, this proves all three clauses.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.IsBirationalVia`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.closure`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.improperMarginal`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.mpsState`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.openBoundaryMPS`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.result`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.vanishingPolys`
- Dependency: [D5/S3/Analytic/Hunter/NCHunterPositivity](../../Analytic/Hunter/NCHunterPositivity.md)
