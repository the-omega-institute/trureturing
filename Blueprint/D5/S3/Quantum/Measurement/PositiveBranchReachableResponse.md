# Positive Branch Reachability and Response

## Abstract

Strictly positive branch weights preserve the original Kraus word support. Termination from one initial positive matrix then controls every state on its reachable space, uniformly on compact parameter sets.

For finite index sets n and A, let K_a be complex n by n matrices, let c_a be strictly positive real weights, and let rho be positive semidefinite. Write T(X) = sum_a c_a K_a X K_a^*, R_l = sum_{k=0}^l T^k(rho), and supp(X) = ker(X) perpendicular. The empty Kraus word is the identity. W_l(K,rho) is the complex span of K_w v for words of length at most l and v in supp(rho); S(K,rho) is the union, equivalently the supremum, of these increasing subspaces. Quadratic forms use the Euclidean inner product and their real parts.

**Theorem 1.1 (Finite orbits and original words).**

$$\forall n: Type, \forall A: Type, \operatorname{Finite}(n) \land \operatorname{Finite}(A) \Rightarrow \forall K: A \to M_{n}(\mathbb{C}), \forall c: A \to \mathbb{R}, \forall \rho: M_{n}(\mathbb{C}), \operatorname{Positive}(c) \land \rho \geq 0 \Rightarrow \forall L: \mathbb{N}, \operatorname{supp}(\operatorname{R}(K, c, \rho, L)) = \operatorname{W}(K, \rho, L)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.finite_orbit_support_eq_word_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive weighted sum has zero quadratic form exactly when every summand has zero quadratic form. Applying this to rho + T(R_l) identifies its kernel with the vectors killed by rho after every adjoint Kraus word of length at most l+1. Taking orthogonal complements gives the support equality for each l. Strict positivity of every weight is essential; no normalization or completeness is needed.

**Theorem 1.2 (A finite faithful sum on the reachable space).**

$$\forall n: Type, \forall A: Type, \operatorname{Finite}(n) \land \operatorname{Finite}(A) \Rightarrow \forall K: A \to M_{n}(\mathbb{C}), \forall c: A \to \mathbb{R}, \forall \rho: M_{n}(\mathbb{C}), \operatorname{Positive}(c) \land \rho \geq 0 \Rightarrow \exists L: \mathbb{N}, \exists \mu: \mathbb{R}, 0 < \mu \land \operatorname{supp}(\operatorname{R}(K, c, \rho, L)) = \operatorname{S}(K, \rho) \land \forall v \in \operatorname{S}(K, \rho), \mu \Vert v\Vert^{2} \leq \operatorname{Re}(\langle v, \operatorname{R}(K, c, \rho, L) v \rangle)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.finite_reachable_faithful_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The increasing word spans stabilize in a finite dimensional space. Choose L after stabilization. The support equality identifies supp(R_L) with S(K,rho). A positive semidefinite operator has a strictly positive quadratic form on the unit sphere of its support; compactness gives a uniform lower bound mu. When rho is zero, the reachable space is zero and any positive mu works.

**Theorem 1.3 (From one terminating state to a common block gap).**

$$\forall d: \mathbb{N}, \forall A: Type, \operatorname{Finite}(A) \Rightarrow \forall K: A \to M_{d}(\mathbb{C}), \forall c: A \to \mathbb{R}, \forall \rho: M_{d}(\mathbb{C}), \operatorname{Positive}(c) \land \rho \geq 0 \land \operatorname{Dual}(K, c, 1) \leq 1 \land \operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, c), k, \rho)) \to 0 (k \to \infty) \Rightarrow \exists N: \mathbb{N}, 1 \leq N \land (\forall v \in \operatorname{S}(K, \rho), \operatorname{Re}(\langle v, \operatorname{Survival}(K, c, N) v \rangle) \leq \frac{\Vert v\Vert^{2}}{2}) \land \forall \sigma: M_{d}(\mathbb{C}), \sigma \geq 0 \land \operatorname{supp}(\sigma) \subseteq \operatorname{S}(K, \rho) \Rightarrow \operatorname{Re}(\operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, c), N, \sigma))) \leq \frac{\operatorname{Re}(\operatorname{Tr}(\sigma))}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.initial_termination_uniform_reachable_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume T^*(I) <= I, with adjoint taken in the trace pairing. The survival effects (T^*)^k(I) decrease to a positive fixed effect F. Termination of the original rho gives Tr(rho F)=0, hence F kills the range of the finite faithful orbit sum and therefore all of S(K,rho). Convergence on its unit sphere gives a block N >= 1 with survival at most one half. The spectral decomposition of any supported positive matrix transports the quadratic bound to its trace. No return effect is assumed to preserve S, and termination is not assumed for arbitrary ambient states.

For a topological parameter space Theta and U contained in Theta, now let c(theta,a) be continuous and strictly positive on U. Keep K_a and the positive return matrices E_a fixed, and assume T_theta^*(I) + sum_a c(theta,a) E_a = I throughout U. Fix theta_0 in U and the same positive rho, terminating at theta_0. In the following formula P(theta,X) denotes sum_{k>=0} T_theta^k(X), J_theta = I - T_theta^*(I), and V(K,rho) is the real span of all positive matrices supported on S(K,rho). Summability always refers to the entire displayed sequence. For each compact nonempty B contained in U, g(B) = min(1, inf_{theta in B} inf_{a in A} c(theta,a)/c(theta_0,a)); an empty branch family uses g(B)=1.

**Theorem 1.4 (All internal parameters and compact geometric tails).**

$$\forall d: \mathbb{N}, \forall A: Type, \forall Theta: Type, \operatorname{Finite}(A) \land \operatorname{TopologicalSpace}(Theta) \Rightarrow \forall K: A \to M_{d}(\mathbb{C}), \forall E: A \to M_{d}(\mathbb{C}), \forall c: Theta \to A \to \mathbb{R}, \forall U: \operatorname{Set}(Theta), \forall \theta_{0}: Theta, \forall \rho: M_{d}(\mathbb{C}), (\forall a: A, \operatorname{E}(a) \geq 0) \land (\forall \theta: U, \forall a: A, 0 < \operatorname{c}(\theta, a)) \land (\forall a: A, \operatorname{ContinuousOn}(\theta \mapsto \operatorname{c}(\theta, a), U)) \land (\forall \theta: U, \operatorname{Dual}(K, \operatorname{c}(\theta), 1)+\operatorname{Sum}(a \in A, \operatorname{c}(\theta, a) \operatorname{E}(a)) = 1) \land \theta_{0} \in U \land \rho \geq 0 \land \operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta_{0})), k, \rho)) \to 0 (k \to \infty) \Rightarrow \exists N: \mathbb{N}, 1 \leq N \land (\forall \theta: U, \forall \sigma: M_{d}(\mathbb{C}), \sigma \geq 0 \land \operatorname{supp}(\sigma) \subseteq \operatorname{S}(K, \rho) \Rightarrow \operatorname{Re}(\operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma))) \to 0 (k \to \infty) \land \operatorname{Summable}(k \mapsto \operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma)) \land \operatorname{P}(\theta, \sigma)-\operatorname{T}(K, \operatorname{c}(\theta), \operatorname{P}(\theta, \sigma)) = \sigma \land \forall F: M_{d}(\mathbb{C}), 0 \leq F \leq J_{\theta} \Rightarrow \operatorname{Summable}(k \mapsto \operatorname{Tr}(F \operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma))) \land \operatorname{Sum}(k \mapsto \operatorname{Tr}(F \operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma))) = \operatorname{Tr}(F \operatorname{P}(\theta, \sigma)) \land 0 \leq \operatorname{Re}(\operatorname{Tr}(F \operatorname{P}(\theta, \sigma))) \leq \operatorname{Re}(\operatorname{Tr}(\sigma)) \land (F = J_{\theta} \Rightarrow \operatorname{Tr}(F \operatorname{P}(\theta, \sigma)) = \operatorname{Tr}(\sigma))) \land (\forall \theta: U, \forall X: \operatorname{V}(K, \rho), \operatorname{Summable}(k \mapsto \operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, X)) \land \operatorname{P}(\theta, X)-\operatorname{T}(K, \operatorname{c}(\theta), \operatorname{P}(\theta, X)) = X) \land \forall B: \operatorname{Set}(Theta), \operatorname{Compact}(B) \land B \neq \emptyset \land B \subseteq U \Rightarrow 0 < \operatorname{g}(B) \leq 1 \land (\forall \theta: B, \forall \sigma: M_{d}(\mathbb{C}), \sigma \geq 0 \land \operatorname{supp}(\sigma) \subseteq \operatorname{S}(K, \rho) \Rightarrow \forall k: \mathbb{N}, \operatorname{Re}(\operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma))) \leq (1-\frac{(\operatorname{g}(B))^{N}}{2})^{\lfloor\frac{k}{N}\rfloor} \operatorname{Re}(\operatorname{Tr}(\sigma))) \land \forall \sigma: M_{d}(\mathbb{C}), \sigma \geq 0 \land \operatorname{supp}(\sigma) \subseteq \operatorname{S}(K, \rho) \land \operatorname{Tr}(\sigma) = 1 \Rightarrow \forall k: \mathbb{N}, \operatorname{Sup}(B, \theta \mapsto \operatorname{Re}(\operatorname{Tr}(\operatorname{Iter}(\operatorname{T}(K, \operatorname{c}(\theta)), k, \sigma)))) \leq (1-\frac{(\operatorname{g}(B))^{N}}{2})^{\lfloor\frac{k}{N}\rfloor}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.positive_branch_compact_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One common block N comes from the gap at theta_0. On a compact set B, positivity and continuity give 0 < g(B) <= 1. Comparison of the positive maps and return effects gives I-(T_theta^*)^N(I) >= g(B)^N [I-(T_theta_0^*)^N(I)] on S. Iteration yields the geometric bound with eta = g(B)^N/2. Singletons give termination and summability at every internal parameter. Summing the orbit gives the Poisson equation; continuity of the trace pairing gives the actual event response, its nonnegativity and its mass bound. Taking the full return effect recovers the whole initial trace. Real linearity extends the Poisson identity to V(K,rho).

For a finite fixed source instrument, group the Kraus maps into the original source branches. The weights 1, p, 1-p, q, 1-q are positive on the open source square, so the same reachable space works throughout that square. The block length and compact constants depend on the fixed instrument; they are not asserted to be uniform over different controllers or at source endpoints.

For response coordinates, let Z be the real span of the original CP branch words applied to rho. This space contains rho, is invariant under every source branch and is independent of p and q. It lies in the Hermitian matrices supported on S. Thus D = dim_R Z <= dim_C(S)^2 <= d^2. Fix one real basis of Z. The preceding summable Poisson identity restricts to Z: the sum of the iterates is an inverse of I-M_theta. Finite dimensional injectivity and surjectivity agree, so this inverse exists on all of Z, including directions outside the positive cone.

For an event with initial mass gamma_E and return effect F_E,theta, the actual probability is gamma_E + ell_E,theta (I-M_theta)^{-1} rho_V, where ell_E,theta(X)=Tr(F_E,theta X). The source conditions gamma_E >= 0, gamma_E+Tr(rho) <= 1 and 0 <= F_E,theta <= J_theta put this response in [0,1]. Along an affine physical source line, M_theta and ell_E,theta have real affine entries. The determinant denominator has degree at most D and is nonzero on the open physical segment. The adjugate has degree at most D-1, so the numerator, including the initial mass term, also has degree at most D. The response is real analytic there. If D=0 the response is constant.

For the four-cell target with B equal to 2 or 4, 1 <= C <= 1024/225, beta > 0 and 0 < h <= 1/4, the legal c=1 subfamily already obstructs a finite dimensional fixed source instrument. Only fresh classical source outcomes carry the unknown rates; the Kraus maps, terminal effects and initial data are fixed. For the chosen request the target mass of (x,z) is u_x/2 + (h^beta/16)(-1)^(x+z), with u_1 the requested source rate and u_0=1-u_1. On c=1, p=q=t=(1-h/C)/B, so the (1,0) response must equal f(t)=t/2-[C(1-Bt)]^beta/16 on ((1-1/(4C))/B,1/B). The rational response must remain a probability on the full internal source interval. Analytic continuation of the target marginal toward zero forces a negative response at positive internal rates, contradicting nonnegativity. This argument includes positive integer beta.

For a fixed dimension cap d, a hypothetical sequence of controllers with uniform total variation error tending to zero would give rational functions of degrees bounded by d^2. Normalize each numerator-denominator coefficient pair to norm one and pass to a convergent subsequence. The full interval probability bounds exclude a zero limiting denominator; on an open interval avoiding its finitely many roots, the limit equals the target. The same analytic and nonnegativity obstruction yields a contradiction. Hence the uniform error has a strictly positive lower bound for each d. This conclusion gives no rate and does not require a compact parameter space of quantum realizations or a quantum realization of the limiting rational function.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.finite_orbit_support_eq_word_span`
- Truth anchor: `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.finite_reachable_faithful_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.initial_termination_uniform_reachable_gap`
- Truth anchor: `D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.positive_branch_compact_absorption`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit](GeneralInstrumentSurvivalLimit.md)
- Dependency: [D5/S3/Quantum/Measurement/IncoherentCone](IncoherentCone.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
