# Critical scalar identities have three source directions

## Abstract

Critical scalar identities have three source directions

**Theorem 1.1 (Polynomial multiplication forces dimension growth).**

Lean statement: `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota be any finite type, t:iota to the reals injective, and V,K real linear subspaces of real functions on iota. Suppose a belongs to V and every a(i) is nonzero. If for every v in V and every natural j at most d the function v(i)*t(i)^j belongs to K, then dim(K) is at least min(card(iota),dim(V)+d). Repeatedly enlarge V by its image under coordinatewise multiplication by t. An enlargement that stops is invariant under that multiplication. It contains all clock powers of a, and Lagrange interpolation then makes it the entire function space. Thus each proper enlargement increases dimension by at least one. This argument supplies the critical scalar-span contradiction with a scalar-kernel observation space, including restriction away from its identically zero coordinates.

**Theorem 1.2 (A nonzero universal scalar identity forces cumulative span three).**

Lean statement: `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every declared degree d at least one, every legal Boolean word w containing both M and J with exactly 2*(d+1)+1 initial-inclusive original-clock reads, and every fixed whole-coefficient readout C, suppose C annihilates constant drift, its auxiliary response at every real 2 by 2 matrix T equals scalarFunctional(T) times the identity, and this functional is nonzero. Then the real span of all actual cumulative matrices acquisition(take(i,w)) has dimension exactly three. The hypotheses are the original GainRay response and scalar functional, with every original prefix and clock retained.

Mixedness already gives dimension at least three. If the span were four, trace pairing would make the scalar-kernel observation map injective, with three-dimensional image. A single scalar-kernel source realizes exactly the coordinates Q whose cumulative matrices are proportional to the scalar representative. The even-word proportionality bound gives card(Q) at most d+1. On the complementary coordinates the image contains a vector with every coordinate nonzero. All its polynomial multiples through degree d come from responseMatrix and lie in the restricted readout kernel. When Q is empty this kernel has dimension at most d+2. When Q is nonempty the constant drift vector makes the subspace vanishing on Q proper, so its dimension is at most d+1. Polynomial dimension growth contradicts both bounds.

On the full original world domain, `D5/S3/Observer/Linear/GainRayNuisance.universal_scalar_identity` supplies drift annihilation and the auxiliary response identity from universal coefficient collinearity. `D5/S3/Observer/Linear/GainRayNuisance.successful_scalar_nonzero` supplies nonzeroness at any actual successful world. These statements retain every nonzero coefficient vector, including degree drops and sampled roots, and arbitrary real drift.

For the complete-target application, let d be any integer at least one and let P be any original Protocol d. Attach any answer function from each complete literal History w to a real 2 by 2 matrix, an ordinary real polynomial and a real drift. Require that at every original World d an actual terminal word w and its selected matrix C have at most 2*d+3 initial-inclusive reads, that C returns a nonzero scalar multiple of the whole original coefficient vector, and that the answer at this same history equals the actual source, gain polynomial and drift. These simultaneous requirements are inconsistent. Actions, stopping, answers and matrix selection are arbitrary history functions; the palettes alone are preassigned countable sets of fixed matrices.

To obtain a common contradiction subdomain, put L=2*(d+1), M=action false, J=action true and T_a(S)=(M^a)^(-1)*S.transpose*M^a. Similarity and transpose preserve rank and trace. The symmetric positive Perron projector S_*=sourceChart(phi,phi) is fixed by every T_a. For P_r=sourceChart(phi,r), native matrix powers give M^a*P_r=s_a*P_r with s_a>0. Consequently T_a(P_r)=P_r exactly when P_r is symmetric, which for positive r is exactly r=phi. For the finitely many a=0,...,L, strict entry positivity of T_a persists near S_*. Restrict this neighborhood to the line x=phi and choose r>phi sufficiently close to phi. All T_a(P_r) are positive and distinct from P_r, and the two diagonal entries of P_r differ. Define V_L in the full positive (x,r) chart by requiring all those strict positivities and nonfixities, together with unequal diagonal entries. These are finitely many open conditions, and the chosen point belongs to V_L. Thus V_L is a nonempty open subset of the full two-dimensional chart, rather than merely a line. Each T_a is legal there, as is R(S)=J*S.transpose*J; R permutes the diagonal entries, preserves the off-diagonal entries and is distinct by the diagonal condition. Partners need only be legal in the original full source domain.

The word-plane argument uses the first switch only. If a mixed word starts with k>0 copies of action a and then action (!a), its cumulative span contains the three independent matrices I, action a and action (!a)*(action a)^k. The independence is the one used in `D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span`. If the whole cumulative span has dimension three, it equals their span. With A=(action a)^k, the partner A^(-1)*S.transpose*A has equal trace pairings on all three generators, hence on every actual prefix. For a=M it is T_k; for a=J it is T_0 when k is even and R when k is odd. The bound on actions gives k<=L. Pure words have symmetric cumulative matrices by `D5/S3/Observer/Linear/GainRayHistory.acquisition_pure`, so T_0 supplies their distinct equal-trace partners on this same V_L. No classification of later letters is needed.

Keep the exact same whole nonzero coefficient vector and real drift in the partner world. Equal source trace pairings then give equal complete readings at every original clock, including the initial read and each immediate read; roots, signs and lower actual degrees cause no exception. `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer` transfers the reached word and its stopping decision. Whole-domain correctness applies to both worlds. Applying `D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached` in both directions identifies the transferred terminal word with the terminal word supplied by correctness. The arbitrary answer function must therefore give the same answer for two distinct actual sources. This rules out pure terminal words and every three-dimensional mixed terminal word on V_L, without regularity assumptions on any decision or answer.

For each word and each matrix in its preassigned palette, distinguish universal coefficient collinearity from its failure. Under universality, a successful bounded mixed terminal word with at most 2*(d+1) reads contradicts `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`. At exactly 2*(d+1)+1 reads, the critical scalar-span theorem forces dimension three and the partner contradiction applies. Pure terminal words are already excluded. A universally collinear pair can therefore be assigned the constant polynomial one: it has no bounded successful terminal world on the chosen domain. For each remaining pair, `D5/S3/Observer/Linear/GainRayNuisance.chart_wedge_nonzero_iff` supplies a nonzero chart wedge, and `D5/S3/Observer/Linear/GainRayNuisance.success_chart_wedge_zero` makes that polynomial vanish at every actual success for this pair.

All Boolean words form a countable set, and every word palette is countable, so all word-matrix pairs are countable. The parameter set V_L times the nonzero whole coefficient vectors times the real drift is nonempty and open in the actual d+4 real chart coordinates. Apply `D5/S3/Observer/Linear/GainRayAdaptive.countable_polynomial_avoidance` to the selected nonzero polynomials on this open set. The resulting original world avoids every selected zero set. Its actual bounded successful terminal pair, required by correctness, belongs to one of those zero sets, giving the contradiction. This proves the mechanism-specific complete-target exclusion through 2*d+3 reads, and hence the integer lower bound 2*d+4. It provides neither a matching complete-target upper construction nor an exclusion of unrestricted nonlinear gain-output mechanisms; the countable fixed-linear output contract is essential.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.countable_polynomial_avoidance`
- Truth anchor: `D5/S3/Observer/Linear/GainRayCriticalSpan.critical_scalar_span`
- Truth anchor: `D5/S3/Observer/Linear/GainRayCriticalSpan.weighted_polynomial_span_growth`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.acquisition_pure`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.identical_prefix_transfer`
- Truth anchor: `D5/S3/Observer/Linear/GainRayHistory.terminal_extends_reached`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.chart_wedge_nonzero_iff`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.mixed_scalar_obstruction`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.success_chart_wedge_zero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.successful_scalar_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayNuisance.universal_scalar_identity`
- Truth anchor: `D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span`
- Dependency: [D5/S3/Observer/Linear/GainRayNuisance](GainRayNuisance.md)
