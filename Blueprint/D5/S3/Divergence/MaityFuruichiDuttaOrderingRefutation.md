# The proposed noncommuting Tsallis bound order fails

## Abstract

A noncommuting positive definite qubit pair reverses the proposed Tsallis bound order.

**Definition 1.1 (The deformed logarithm).**

$$\forall (r: \mathbb{R}), \forall (x: \mathbb{R}), \operatorname{lnr}\left(r, x\right) = (\frac{(x^{r}) - (1)}{r})$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.lnr` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Definition 1, printed p. 2: “The r-logarithm is denoted by ln_r(x) and it is defined by ln_r(x) = (x^r − 1)/r, for r ≠ 0 and x ≥ 0.” The real power is Real.rpow.

**Definition 1.2 (The deformed Rényi relative entropy).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) = ((\frac{1}{(alpha) - (1)}) \cdot (\operatorname{lnr}\left(r, (\operatorname{Matrix}.\operatorname{trace} (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{z}), ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{(1) - (alpha)}{(2) \cdot (z)}}), sigma\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{alpha}{z}}), rho\right))) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{(1) - (alpha)}{(2) \cdot (z)}}), sigma\right))\right))).\operatorname{re}\right)))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.renyiRZ` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Definition 2, printed p. 2: “The r-deformed α-z-Rényi relative entropy for any two positive semi-definite operators ρ and σ with Supp(ρ) ⊆ Supp(σ) is defined by D^{(r)}_{α,z}(ρ||σ) = (1/(α−1)) ln_r Tr[(σ^{(1−α)/(2z)} ρ^{α/z} σ^{(1−α)/(2z)})^z] … where α, r ∈ R and z ∈ R+.” The source calls this quantity B₁. Here n is the dimension, rho and sigma are complex matrices, alpha denotes α, cfc evaluates each real function of a Hermitian matrix, and re takes the real part of its trace.

**Definition 1.3 (The Tsallis relative entropy).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \operatorname{tsallis}\left(alpha, rho, sigma\right) = (\frac{(\operatorname{Matrix}.\operatorname{trace} ((rho) - ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{alpha}), rho\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{(1) - (alpha)}), sigma\right))))).\operatorname{re}}{(1) - (alpha)})$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.tsallis` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equation (6), printed p. 2, gives D_α(ρ||σ) = Tr[ρ − ρ^α σ^{1−α}]/(1 − α). The displayed expression uses cfc for the two matrix powers and the real part of the trace.

**Definition 1.4 (The second upper bound).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \forall (q: \mathbb{R}), \operatorname{B2}\left(alpha, q, rho, sigma\right) = (- ((\operatorname{Matrix}.\operatorname{trace} ((rho) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto \operatorname{lnr}\left((1) - (alpha), x\right)), \operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{1}{q}}), ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{- (\frac{q}{2})}), rho\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{q}), sigma\right))) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{- (\frac{q}{2})}), rho\right))\right)\right)))).\operatorname{re}))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equations (8) and (47), printed pp. 2 and 11, give B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})]. Each real matrix function is evaluated by cfc, with the negative sign outside the real trace.

**Definition 1.5 (The source's proposed ordering).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((rho).\operatorname{PosDef}) \Rightarrow (((rho).\operatorname{trace} = (1)) \Rightarrow (((sigma).\operatorname{PosDef}) \Rightarrow (((sigma).\operatorname{trace} = (1)) \Rightarrow (((rho) \cdot (sigma) \ne (sigma) \cdot (rho)) \Rightarrow (\forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \forall (q: \mathbb{R}), (0 \le alpha) \Rightarrow ((alpha < 1) \Rightarrow ((r \ne 0) \Rightarrow ((0 < z) \Rightarrow (((1) - (alpha) < q) \Rightarrow ((\operatorname{tsallis}\left(alpha, rho, sigma\right) \le \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right)) \land (\operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) \le \operatorname{B2}\left(alpha, q, rho, sigma\right)))))))))))))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equations (8)–(9), printed p. 2: “For 0 ≤ α < 1 and q > (1 − α), we compare two upper bounds B₁(ρ||σ) = D^{(r)}_{α,z}(ρ||σ) and B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})] of the Tsallis relative entropy, numerically. We observe that for non-commutative density operators ρ and σ, D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ).” Section 4, Case 5, printed p. 12: “Let Tr(ρ) = 1 and Tr(σ) = 1, that is both ρ and σ are density operators. Here, we numerically observe that for any two operators ρ and σ, B₁(ρ||σ) is a tighter bound of Tsallis relative entropy than B₂(ρ||σ).” The formula ranges over every finite dimension. Positive definite matrices with unit trace satisfy the support condition and admit negative powers. The parameters r≠0 and z>0 come from Definitions 1–2. The function renyiRZ is precisely the source's B₁.

**Definition 1.6 (Existing supporting declaration rho).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.rho`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rho supplies the common-basis application below.

Complete Lean statement: def rho : Matrix (Fin 2) (Fin 2) ℂ := !![4/5, 0; 0, 1/5]

**Definition 1.7 (Existing supporting declaration sigma).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sigma`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sigma supplies the common-basis application below.

Complete Lean statement: def sigma : Matrix (Fin 2) (Fin 2) ℂ := !![28/125, (6 * Real.sqrt 6 : ℝ) / 125;   (6 * Real.sqrt 6 : ℝ) / 125, 97/125]

**Definition 1.8 (Existing supporting declaration H).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.H`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The H supplies the common-basis application below.

Complete Lean statement: def H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

**Definition 1.9 (Existing supporting declaration K).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.K`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The K supplies the common-basis application below.

Complete Lean statement: def K : Matrix (Fin 2) (Fin 2) ℂ := !![-23/25, (4 * Real.sqrt 6 : ℝ) / 25;   (4 * Real.sqrt 6 : ℝ) / 25, 23/25]

**Theorem 1.10 (Existing supporting declaration pair_states).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_states`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair_states supplies the common-basis application below.

Complete Lean statement: lemma pair_states : rho.PosDef ∧ rho.trace = 1 ∧     sigma.PosDef ∧ sigma.trace = 1 ∧ rho * sigma ≠ sigma * rho

**Theorem 1.11 (Existing supporting declaration pair_cfc).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_cfc`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_cfc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair_cfc supplies the common-basis application below.

Complete Lean statement: lemma pair_cfc (f : ℝ → ℝ) :     cfc f rho = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +       ((f (4/5) - f (1/5))/2) • H ∧     cfc f sigma = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +       ((f (4/5) - f (1/5))/2) • K

**Theorem 1.12 (Existing supporting declaration sandwich_trace).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sandwich_trace supplies the common-basis application below.

Complete Lean statement: lemma sandwich_trace :     (trace (cfc (fun x:ℝ => x^(2:ℝ))       (cfc (fun x:ℝ => x^(1/8:ℝ)) sigma * cfc (fun x:ℝ => x^(1/4:ℝ)) rho *         cfc (fun x:ℝ => x^(1/8:ℝ)) sigma))).re =       (2117 + 288 * Real.sqrt 2) / 3125

**Theorem 1.13 (Existing supporting declaration B1_gt).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B1_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B1_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B1_gt supplies the common-basis application below.

Complete Lean statement: lemma B1_gt : (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rho sigma

**Theorem 1.14 (Existing supporting declaration B2_lt).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B2_lt supplies the common-basis application below.

Complete Lean statement: lemma B2_lt : B2 (1/2) 1 rho sigma < (2/5:ℝ)

**Definition 1.15 (Existing supporting declaration A).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A`

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The A supplies the common-basis application below.

Complete Lean statement: def A : Matrix (Fin 2) (Fin 2) ℂ := !![7/25, (3 * Real.sqrt 6:ℝ)/25;   (3 * Real.sqrt 6:ℝ)/25, 97/25]

**Theorem 1.16 (Existing supporting declaration sandwich_A).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_A`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sandwich_A supplies the common-basis application below.

Complete Lean statement: lemma sandwich_A :     cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho * sigma *       cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho = A

**Theorem 1.17 (Existing supporting declaration A_nonneg).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The A_nonneg supplies the common-basis application below.

Complete Lean statement: lemma A_nonneg : (0:Matrix (Fin 2) (Fin 2) ℂ) ≤ A

**Theorem 1.18 (Existing supporting declaration A_sqrt).**

Lean statement: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The A_sqrt supplies the common-basis application below.

Complete Lean statement: lemma A_sqrt : cfc (fun x:ℝ => x^(1/2:ℝ)) A =     (5 / Real.sqrt 154:ℝ) • (A + 1)

**Theorem 1.19 (A noncommuting qubit counterexample).**

$$\neg (\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((rho).\operatorname{PosDef}) \Rightarrow (((rho).\operatorname{trace} = (1)) \Rightarrow (((sigma).\operatorname{PosDef}) \Rightarrow (((sigma).\operatorname{trace} = (1)) \Rightarrow (((rho) \cdot (sigma) \ne (sigma) \cdot (rho)) \Rightarrow (\forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \forall (q: \mathbb{R}), (0 \le alpha) \Rightarrow ((alpha < 1) \Rightarrow ((r \ne 0) \Rightarrow ((0 < z) \Rightarrow (((1) - (alpha) < q) \Rightarrow ((\operatorname{tsallis}\left(alpha, rho, sigma\right) \le \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right)) \land (\operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) \le \operatorname{B2}\left(alpha, q, rho, sigma\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/maity-furuichi-dutta-2026-tsallis-ordering-case-5` (refuted) by `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"maity-furuichi-dutta-2026-tsallis-ordering-case-5","declaration_gid":"D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Take rho = diag(4/5,1/5) and sigma = (1/125)[[28,6√6],[6√6,97]]. Both matrices are positive definite with unit trace, and they do not commute. At alpha = r = 1/2, z = 2 and q = 1, the proof gives 2/5 < renyiRZ(alpha,r,z,rho,sigma) and B2(alpha,q,rho,sigma) < 2/5. For the first value the trace inside the deformed logarithm is (2117+288√2)/3125, so B₁ = 4(1−√((2117+288√2)/3125)). For the second, put A = (1/25)[[7,3√6],[3√6,97]]. Its positive square root is (5/√154)(A+1), giving B₂ = 2−20/√154. These inequalities contradict the second conjunct of the proposed order. The inequality tsallis≤renyiRZ is not refuted here.

## Application: both states nondiagonal in one common basis

Haobo Ma and Wenlin Zhang's supplement, A Tsallis-bound counterexample with both states nondiagonal (CC BY 4.0), answers Supriyo Dutta's common-basis question. Its source and license are recorded in the accompanying Library note. Supriyo Dutta is distinct from Soumyojyoti Dutta and Tushar. The following application uses the definitions and pair computations above; it is a presentation of their consequences, not another conjecture resolution.

### The common orthogonal transformation and density matrices

All displayed 2 by 2 matrices are complex matrices with real entries, indexed by Fin 2. Write X* for conjugate transpose and I for the identity. Set U = (1/√2)[[1,1],[1,−1]], ρ̂ = (1/10)[[5,3],[3,5]] and σ̂ = (1/250)[[125+12√6,−69],[−69,125−12√6]]. Because U is real symmetric and [[1,1],[1,−1]]² = 2I, U* = U and U² = I. Thus U is real orthogonal and, over the complex numbers, unitary.

For the existing ρ = diag(4/5,1/5) and σ = (1/125)[[28,6√6],[6√6,97]], multiplication gives UρU* = (1/10)[[5,3],[3,5]] = ρ̂ and UσU* = (1/250)[[125+12√6,−69],[−69,125−12√6]] = σ̂. The same U acts on both matrices. The existing pair_states supplies positive definiteness and trace one of ρ and σ. Unitary congruence preserves positive definiteness (Unitary.isUnit_coe and posDef_star_right_conjugate_iff), and cyclicity preserves trace. Therefore ρ̂ and σ̂ are positive definite density matrices. In particular, they are full rank, their supports agree, and their negative powers are defined spectrally.

Directly, Tr ρ̂ = 5/10+5/10 = 1 and Tr σ̂ = (125+12√6+125−12√6)/250 = 1. Their determinants are (25−9)/100 = 4/25 and (125²−(12√6)²−69²)/250² = (15625−864−4761)/62500 = 4/25. For either matrix, Matrix.charpoly_fin_two gives X²−X+4/25 = (X−4/5)(X−1/5), over the complex numbers. Hence each has the distinct eigenvalues 4/5 and 1/5, each with algebraic multiplicity one.

Both off-diagonal entries of ρ̂ are 3/10, and both off-diagonal entries of σ̂ are −69/250; all four entries are nonzero. Matrix multiplication gives [ρ̂,σ̂] = ρ̂σ̂−σ̂ρ̂ = (18√6/625)[[0,−1],[1,0]]. In particular [ρ̂,σ̂]₀₁ = −18√6/625 ≠ 0, since √6 > 0. Also [ρ̂,σ̂] = U[ρ,σ]U*, using U*U = I. Thus noncommutation is preserved, whereas the nonzero off-diagonal entries refer to this chosen common basis.

### Covariance of the actual functional calculus

More generally, for every natural n, every unitary u in Matrix (Fin n) (Fin n) ℂ, every real function f : ℝ → ℝ and every complex matrix X of that size, set e = Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) u, so e(X) = uXu*. Then e(cfc f X) = cfc f (e X). For self-adjoint X, use StarAlgHomClass.map_cfc with p = q = IsSelfAdjoint: finite_real_spectrum.continuousOn supplies continuity of any f on the finite real spectrum, and continuous_of_finiteDimensional supplies continuity of e. Self-adjointness is preserved by e. If X is not self-adjoint, injectivity of e reflects self-adjointness, so e X is not self-adjoint either; cfc_apply_of_not_predicate makes both cfc values zero, and map_zero completes the identity. No continuity assumption on f or positivity assumption on X is needed for this total-cfc identity.

For every such n and u, every pair ρ, σ of complex matrices, and every real α, r, z, q, the existing definitions satisfy renyiRZ α r z (e ρ) (e σ) = renyiRZ α r z ρ σ, B2 α q (e ρ) (e σ) = B2 α q ρ σ, and tsallis α (e ρ) (e σ) = tsallis α ρ σ. Indeed e preserves products and differences, and Tr(e X) = Tr(uXu*) = Tr(u*uX) = Tr X by Matrix.trace_mul_cycle and u*u = I. Apply the cfc identity to each real power and to x ↦ lnr (1−α) x, move e through the matrix products, then remove it under the trace. Real parts and the scalar factors in lnr, renyiRZ, B2 and tsallis are unchanged. These algebraic identities also cover the total definitions at singular or exceptional parameters; their entropy interpretation uses the source hypotheses stated above. In particular, for our U, cfc f (UXU*) = U(cfc f X)U* for every real f and every complex 2 by 2 X.

### Source parameters and transported spectral quantities

Take α = r = 1/2, z = 2 and q = 1. The source conditions are 0 ≤ 1/2 < 1, r = 1/2 ≠ 0, z = 2 > 0 and q = 1 > 1−α = 1/2. Use B₁ = renyiRZ(1/2,1/2,2,ρ̂,σ̂), B₂ = B2(1/2,1,ρ̂,σ̂) and D = tsallis(1/2,ρ̂,σ̂), with exactly the existing definitions. The exponents (1−α)/(2z), α/z, z are respectively 1/8, 1/4, 2, and −q/2, q, 1/q are −1/2, 1, 1.

Define F = Re Tr[(σ̂^(1/8) ρ̂^(1/4) σ̂^(1/8))²], with every matrix power meaning cfc (x ↦ x^t), using Real.rpow. Covariance transports this entire expression to the original pair, so the existing sandwich_trace gives F = (2117+288√2)/3125. The same covariance and the existing sandwich_A give ρ̂^(−1/2) σ̂ ρ̂^(−1/2) = UAU*, where A = (1/25)[[7,3√6],[3√6,97]]. The existing A_nonneg and A_sqrt give A ≥ 0 and √A = (5/√154)(A+I); hence the square root of the transformed sandwich is U[(5/√154)(A+I)]U*. These are the actual spectral expressions inside the two bounds, not substituted scalar definitions.

### Exact bound and Tsallis calculations

Since lnr(1/2,x) = 2(√x−1) for x ≥ 0 and 1/(α−1) = −2, B₁ = 4(1−√F) = 4(1−√((2117+288√2)/3125)). For B₂, q = 1 removes the outer 1/q power, and the deformed logarithm is 2(√A−I). Direct evaluation with the existing ρ and A gives Tr(ρA) = 28/125+97/125 = 1, Tr ρ = 1 and Tr(ρ√A) = (5/√154)Tr(ρ(A+I)) = 10/√154. Consequently B₂ = −2 Re Tr[ρ(√A−I)] = 2−20/√154, with the same value for the hatted pair by simultaneous conjugation.

For D, apply the existing pair_cfc to f(x) = √x. Its values at the two eigenvalues are f(4/5) = 2/√5 and f(1/5) = 1/√5. With H = [[1,0],[0,−1]] and K = (1/25)[[−23,4√6],[4√6,23]], this gives √ρ = (3I+H)/(2√5) and √σ = (3I+K)/(2√5). Here Tr H = Tr K = 0 and Tr(HK) = −46/25. Thus Re Tr(√ρ√σ) = (18−46/25)/20 = 101/125. The existing tsallis definition now gives D = 2(1−101/125) = 48/125. Covariance gives this same value for ρ̂ and σ̂.

The existing B2_lt and B1_gt give B₂ < 2/5 < B₁. Explicitly, 154 < (25/2)² gives √154 < 25/2 and hence B₂ < 2/5. Also √2 < 17/12 gives 0 < F < 2525/3125 = 101/125 < 81/100, so √F < 9/10 and B₁ > 2/5. To compare D with B₂, 1250² = 1562500 < 1570954 = 154·101² implies √154 > 1250/101. Therefore 20/√154 < 202/125 and D = 48/125 < 2−20/√154 = B₂. Together D < B₂ < 2/5 < B₁, and in particular D < B₂ < B₁. Both displayed quantities are strict upper bounds for D at this pair.

### Restricted comparison and scope

Consider the universally quantified comparison over all complex 2 by 2 matrices ρ, σ with ρ.PosDef, Tr ρ = 1, σ.PosDef, Tr σ = 1, ρσ ≠ σρ, ρ₀₁ ≠ 0 and σ₀₁ ≠ 0: renyiRZ(1/2,1/2,2,ρ,σ) ≤ B2(1/2,1,ρ,σ). The pair ρ̂, σ̂ satisfies every hypothesis, whereas B₂ < B₁ contradicts that conclusion. Thus even this restriction to two states nondiagonal in the same basis is false. This is a consequence of the existing refutation and its common-basis application; it adds no independently asserted Lean theorem. It makes no assertion of an ordering at other parameters, refutes neither D ≤ B₁ nor the source's commuting comparison, and does not assert a physical preparation protocol, a resource advantage, or literature novelty. Nondiagonality is basis dependent; noncommutation and all three values are invariant under a simultaneous unitary change of basis.

## References

- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_nonneg`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.A_sqrt`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B1_gt`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2_lt`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.H`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.K`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.lnr`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_cfc`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.pair_states`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.renyiRZ`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.rho`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_A`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sandwich_trace`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.sigma`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.tsallis`
- Dependency: [D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus](../Quantum/Matrix/TwoPointFunctionalCalculus.md)
