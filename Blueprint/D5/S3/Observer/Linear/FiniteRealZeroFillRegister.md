# Finite Real Zero-Fill Register

## Abstract

A finite real zero-fill register reads every original sign through its horizon.

**Definition 1.1 (Infinite binary inputs).**

$$X:=(\mathbb{N}\to\mathrm{Bool})$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An input is an arbitrary function from natural times to Bool; no finite encoding or probability measure is imposed.

**Definition 1.2 (The original real sign).**

$$\begin{gathered}\forall b\in \mathrm{Bool},\quad \operatorname{bitSign}(b)=(-1)^{\operatorname{toNat}(b)}\in \mathbb{R}\\{}\operatorname{bitSign}(\operatorname{false})=+1,\quad \operatorname{bitSign}(\operatorname{true})=-1\end{gathered}$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.bitSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original sign is minus one raised to the Boolean natural value: false has sign +1 and true has sign -1.

**Definition 1.3 (The time-indexed original signal).**

$$\forall t\in \mathbb{N}, \forall x\in X,\quad \operatorname{signal}(t,x)=\operatorname{bitSign}(x(t))$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.signal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time t the signal reads the sign of the original input coordinate x(t).

**Definition 1.4 (The finite real state).**

$$\forall H\in \mathbb{N},\quad \operatorname{State}(H):=(\operatorname{Fin}(H+1)\to\mathbb{R})$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any natural horizon H, the state is the real vector with coordinates Fin(H+1). Its entries are arbitrary real numbers; H=0 still has coordinate zero.

**Definition 1.5 (Initialization from the original input).**

$$\forall H\in \mathbb{N}, \forall x\in X, \forall i\in \operatorname{Fin}(H+1),\quad \operatorname{initState}(H,x)(i)=\operatorname{signal}(i.\operatorname{val},x)$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.initState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Initialize coordinate i with signal(i,x), thereby storing the first H+1 original signs once.

**Definition 1.6 (A fixed linear update with real-zero fill).**

$$\forall H\in \mathbb{N},\quad \begin{gathered}U_{H}:=\operatorname{update}(H)\in \operatorname{Hom}_{\mathbb{R}}(\operatorname{State}(H),\operatorname{State}(H))\\{}\forall q\in \operatorname{State}(H), \forall i\in \operatorname{Fin}(H+1),\quad U_{H}(q)(i)=\begin{cases}q(\langle i.\operatorname{val}+1,h\rangle),& h:i.\operatorname{val}+1<H+1,\\{}0\in \mathbb{R},& \mathrm{otherwise}\end{cases}\\{}\forall q,v\in \operatorname{State}(H), \forall c\in \mathbb{R},\quad U_{H}(q+v)=U_{H}(q)+U_{H}(v),\quad U_{H}(c\cdot q)=c\cdot U_{H}(q)\end{gathered}$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update copies coordinate i+1 when that coordinate lies in Fin(H+1), and otherwise writes the real number 0. Both additivity and real scalar compatibility are part of this linear map; Hom over the reals denotes the space of real-linear maps. The boundary value is different from the sign of false. The update uses neither time nor a subsequent input sample.

**Definition 1.7 (A fixed linear readout).**

$$\forall H\in \mathbb{N},\quad R_{H}:=\operatorname{readout}(H)\in \operatorname{Hom}_{\mathbb{R}}(\operatorname{State}(H),\mathbb{R}),\quad \forall q\in \operatorname{State}(H),\quad R_{H}(q)=q(0)$$

*Formalization.* `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout is the real-linear coordinate-zero projection on the same finite real state.

**Theorem 1.8 (Every in-bound coordinate of every iterate).**

$$\forall H,t\in \mathbb{N}, \forall q\in \operatorname{State}(H), \forall i\in \operatorname{Fin}(H+1), \forall h_{i}:i.\operatorname{val}+t<H+1,\quad \operatorname{update}(H)^{[t]}(q)(i)=q(\langle i.\operatorname{val}+t,h_{i}\rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all H,t, arbitrary real state q and coordinate i satisfying i.val+t<H+1, the t-fold update at i equals the original q at i.val+t. Induction on t applies the successor equation for function iteration; the in-bound inequality selects the copy branch at the successor step. The statement concerns only in-bound coordinates.

**Theorem 1.9 (Pointwise attainment of the original signal).**

$$\forall H\in \mathbb{N}, \forall x\in X, \forall t\in \mathbb{N}, \forall h_{t}:t\leq H,\quad \operatorname{readout}(H)(\operatorname{update}(H)^{[t]}(\operatorname{initState}(H,x)))=\operatorname{signal}(t,x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.pointwise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the arbitrary-state invariant to the initialized vector at coordinate zero. For every infinite input x and every t<=H, including H=t=0, the fixed readout after t fixed updates is exactly signal(t,x). This is the finite real construction in original theorem 12.4. In the binary-shift source, the unit-word orbit at coordinate j is x(j+word.length); its coordinate-zero sign observation is therefore this same signal at time t. The construction proves the pointwise upper realization. It asserts no lower bound, minimum dimension, state cardinality, after-boundary identity, or almost-everywhere endpoint.

## Original theorem 12.4: source and parameter correspondence

Original theorem 12.4 in docs/develop/theory/COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md concerns the same infinite binary shift as the construction above. The correspondence below applies existing probability, Hilbert-space, dimension and counting results to this document's X, signal, State and initState. The two canonical theorem entries here remain FiniteRealZeroFillRegister.update_iterate and FiniteRealZeroFillRegister.pointwise_attainment. The lower bound and its minimum, counting and linear-feature consequences are applications of the cited sources, rather than additional canonically compiled or frozen theorem entries. The paper proof keeps its stated paper-proof status.

Give Bool its discrete measurable space and put half = 1/2 in the unit interval, fair = ProbabilityTheory.bernoulliMeasure false true half, and μ = MeasureTheory.Measure.infinitePi (fun _ : ℕ => fair) on the actual X = ℕ → Bool. Thus μ is the independent fair product probability measure, not a measure on a finite prefix surrogate. Write a_t(x) = signal(t,x) = (-1)^(x(t).toNat) and E = MeasureTheory.Lp ℝ 2 μ. Measurability follows from measurable_pi_apply and measurable_of_countable applied to bitSign. Since |a_t(x)| = 1 for every x, MemLp.of_bound at bound 1 supplies a_t ∈ L². Define f_t = MemLp.toLp a_t using this witness. MemLp.coeFn_toLp identifies the chosen function representative of f_t with a_t μ-almost everywhere; the class f_t and the pointwise function a_t are kept distinct.

Measure.infinitePi_map_eval specializes at coordinate t to μ.map (fun x => x(t)) = fair. Applying integral_map and integral_bernoulliMeasure to bitSign gives ∫ a_t dμ = (1/2)(+1) + (1/2)(-1) = 0. The theorem iIndepFun_infinitePi, with the same measurable bitSign at each coordinate, makes the actual functions a_t independent. For i ≠ j, IndepFun.integral_fun_mul_eq_mul_integral therefore gives ∫ a_i a_j dμ = 0. For i = j, a_i(x)² = 1 pointwise and μ(X) = 1 give integral 1. L2.inner_def and the AE representative identities now identify ⟨f_i,f_j⟩ with these integrals. Hence orthonormal_iff_ite gives an orthonormal family t ↦ f_t in this actual real L² space; orthonormality is a consequence of the fair product, not a replacement hypothesis.

For the actual input shift F(x)(j) = x(j+1), the orbit is F^t(x)(j) = x(j+t). In D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.lean, binaryObservation reads the coordinate-zero sign, and the unit-word orbit used inside binary_shift_exact_bit_law has exactly this coordinate formula with t = word.length. Thus o(F^t x) = a_t(x) for every x and every natural t, including zero. This identifies the original observation with the signal attained by pointwise_attainment, before passing to any L² class or AE equality.

The lower-bound parameters are arbitrary H,r ∈ ℕ, a finite-dimensional real submodule V of E with finrank ℝ V = r, and a real η < 1. The approximation premise is exactly: for every natural t ≤ H there exists g ∈ V with ‖f_t - g‖₂ ≤ η. It asks for an approximant separately at each time; no common selected family, recurrence for the approximants, or linear dynamics on V is assumed. Time zero always belongs to the horizon, even when H = 0. Its approximant yields 0 ≤ ‖f_0 - g‖₂ ≤ η, so η ≥ 0 is derived rather than added to the premise. This also explains why a negative η cannot satisfy the original assumptions. No positivity assumption on r is needed.

Instantiate Submodule.starProjection_minimal at this V and f_t: P_V = V.starProjection is the orthogonal projection and has residual norm no greater than the norm for any g ∈ V, hence ‖f_t - P_V f_t‖₂ ≤ η. Submodule.norm_sq_eq_add_norm_sq_starProjection, together with Submodule.starProjection_orthogonal, is Pythagoras for that same projection. Since ‖f_t‖₂ = 1 and η ≥ 0, it gives ‖P_V f_t‖₂² = 1 - ‖f_t - P_V f_t‖₂² ≥ 1 - η² for each t ≤ H. These are the projection and energy parameters in the paper argument; the projection's optimality, rather than a new approximation hypothesis, supplies the residual estimate.

Take b = stdOrthonormalBasis ℝ V, indexed by Fin(finrank ℝ V) = Fin r. Apply OrthonormalBasis.sum_sq_inner_right to V.orthogonalProjectionOnto(f_t); Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left identifies its coefficients with ⟨b_j,f_t⟩ in E. Thus ‖P_V f_t‖₂² = ∑_j ⟨b_j,f_t⟩². Apply Orthonormal.sum_inner_products_le to the orthonormal family f restricted along Fin(H+1) → ℕ, the vector b_j, and Finset.univ. Each b_j has norm one, so ∑_(t=0)^H ⟨b_j,f_t⟩² ≤ 1. Finset.sum_comm exchanges the two finite sums. Combining the energy estimate with these finite Parseval and Bessel formulas gives (H+1)(1-η²) ≤ ∑_(t=0)^H ‖P_V f_t‖₂² = ∑_j ∑_(t=0)^H ⟨b_j,f_t⟩² ≤ r. Empty basis sums cover r = 0, and the time set still has H+1 elements when H = 0.

For the attaining construction, the parameter correspondence is q ∈ State H = (Fin(H+1) → ℝ), U = update H, R = readout H and e = initState H. Module.finrank_pi gives finrank ℝ (State H) = H+1. The existing arbitrary-real-state invariant update_iterate and its coordinate-zero consumer pointwise_attainment give R(U^t(e(x))) = a_t(x) for every x and t ≤ H, using one fixed real-linear U and R. At η = 0 the preceding lower bound forces r ≥ H+1. Conversely, the span of f_0,…,f_H has dimension H+1: finite span gives finite dimensionality, orthonormality gives linear independence, and finrank_span_eq_card gives its dimension. It contains all the target classes with error zero, and the pointwise register realizes them in exactly H+1 real coordinates. This establishes the zero-error minimum for the stated common-feature/linear realization setting, with H = 0 included.

The count 2^(H+1) has a different object. Map each Boolean prefix v : Fin(H+1) → Bool to the real vector i ↦ bitSign(v(i)). This map is injective because bitSign distinguishes false and true. Every initState H x is such a vector; conversely, ContractingDigitMemory.prefixStream (H+1) v extends any prefix to an infinite x and yields that vector as initState H x. Thus range(initState H) is exactly the sign-prefix image. Equiv.ofInjective, Nat.card_congr and finite function counting give Nat.card(range(initState H)) = 2^(H+1). This counts initialized vectors only. State H itself consists of arbitrary real vectors, and the formula does not count all states reachable from arbitrary real initial conditions. In particular the real-zero boundary in update is not the sign +1 used to encode a false bit.

For the fixed linear latent application, let φ : Fin r → E be any family of L² feature classes. Define the real-linear synthesis map T : (Fin r → ℝ) → E by T(c) = ∑_j c_j φ_j and fix V = range(T) once for all times. LinearMap.finrank_range_le and Module.finrank_pi give d = finrank ℝ V ≤ r, allowing dependent features and r = 0. Let A : ℝ^r →ₗ[ℝ] ℝ^r and ℓ : ℝ^r →ₗ[ℝ] ℝ be fixed. With e_j = Pi.single j 1, the finite coordinate expansion q = ∑_j q_j e_j gives ℓ(A^t q) = ∑_j ℓ(A^t e_j) q_j for every q and every natural t. The predicted class h_t = T(fun j => ℓ(A^t e_j)) therefore belongs to this same V for all t, even though its coefficients change with t.

To relate that class to actual outputs, use measurable square-integrable initializer coordinates ψ_j representing φ_j, so ψ_j = φ_j as functions μ-almost everywhere. In the special case of the chosen Lp representatives, take ψ_j(x) = φ_j(x). The finite-sum representative identity follows from Lp.coeFn_add, Lp.coeFn_smul and Lp.coeFn_zero by finite-sum induction, including the empty sum when r = 0. Together with the coordinate expansion it gives h_t(x) = ℓ(A^t(fun j => ψ_j(x))) μ-almost everywhere for each t. This is an AE correspondence of representatives, while the finite register's pointwise_attainment remains an equality for every input. If, explicitly, η < 1 and ‖f_t - h_t‖₂ ≤ η for every t ≤ H, apply the lower-bound argument to V at dimension d, with the available witness h_t ∈ V. It yields (H+1)(1-η²) ≤ d ≤ r. Merely specifying linear maps does not supply this approximation premise.

The Mathlib names in this application refer to the repository's lake-manifest.json revision db584cd6d46c92f209a44c0f1c829460d327499d. The product and integration sources are Probability/Distributions/Bernoulli, Probability/Independence/InfinitePi and Probability/Independence/Integration; the L², projection and finite orthonormal-basis sources are MeasureTheory/Function/L2Space, Analysis/InnerProductSpace/Projection/FiniteDimensional and Analysis/InnerProductSpace/PiL2. The dimension and counting applications use the actual real state and initializer defined here. The conclusion requires one common finite feature space and the stated L² approximation. It makes no bound for arbitrary nonlinear decoders, no finite-precision physical implementation claim and no global novelty claim. The original paper's proof boundary is its Convention 16.3; citing it or explaining these applications does not enlarge the two canonical theorem endpoints above.

## References

- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.State`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.X`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.bitSign`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.initState`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.pointwise_attainment`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.readout`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.signal`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update`
- Truth anchor: `D5/S3/Observer/Linear/FiniteRealZeroFillRegister.update_iterate`
