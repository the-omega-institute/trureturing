# D5 source compiled; RegUNVALIDATED

## Abstract

Growing higher-layer quantitative budget repair.

Single repo-prior-exposed source attempt. The D5 source target has a current scoped Lean build; typed Reg mirrors remain unvalidated for kernel/official acceptance, source binding and variation/sensitivity. This does not assert a consensus result or literature novelty. Existing Budget/prefix/fixed arithmetic owners are reused without copying. The three-helper patch is unapplied. Every typed Reg law reproduces its full telescope with a literal readout; enrollment, current source binding and variation/sensitivity evidence remain unvalidated.

**Theorem 1.1 (uniform_beta_and_slope).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All natural j>=2 and all real u>=2. Geometric sums give 1/(2*u^j*log u)<=beta<=1/(u^j*log u). Weighted differentiation and the elementary lower logarithm bound give 0<slope<=2*j and the exact log-beta derivative.

Exact source telescope (D5-compiled): ∀ {j : ℕ} (hj : 2 ≤ j) {u : ℝ} (hu : 2 ≤ u),     1 / (2 * u ^ j * log u) ≤ beta j u ∧       beta j u ≤ 1 / (u ^ j * log u) ∧       0 < logarithmicSlope j u ∧ logarithmicSlope j u ≤ 2 * (j : ℝ) ∧       HasDerivAt (fun v => log (beta j v)) (-logarithmicSlope j u / u) u

**Theorem 1.2 (adjacent_layer_strict).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.adjacent_layer_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.adjacent_layer_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact identity S_j(u)=u*(S_(j-1)(u)+1) and strict logarithm inequalities prove beta_(j-1)(u)>u*beta_j(u), including j=2,u=2.

Exact source telescope (D5-compiled): ∀ {j : ℕ} (hj : 2 ≤ j) {u : ℝ} (hu : 2 ≤ u),     u * beta j u < beta (j - 1) u

**Theorem 1.3 (moving_interval_marginals).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.moving_interval_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.moving_interval_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrate the uniform UPPER slope on the entire real interval. For rho<q<=rho*(1+1/j^2), exp(-2/j)*lambda<=beta_j(q)<lambda and 0<lambda-beta_j(q)<=2*lambda/j. The root itself is excluded even when prime.

Exact source telescope (D5-compiled): ∀ {j : ℕ} (hj : 3 ≤ j) {ρ priceLambda q : ℝ}     (hρ : 2 ≤ ρ) (hLambda : 0 < priceLambda) (hroot : beta j ρ = priceLambda)     (hq : ρ < q) (hqb : q ≤ ρ * (1 + 1 / (j : ℝ) ^ 2)),     exp (-2 / (j : ℝ)) * priceLambda ≤ beta j q ∧ beta j q < priceLambda ∧       0 < priceLambda - beta j q ∧ priceLambda - beta j q ≤ (2 / (j : ℝ)) * priceLambda

**Theorem 1.4 (uniform_root_geometry).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_root_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_root_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the literal root, the exact geometric beta bounds give X*L/2<=rho^j*log rho<=X*L and L+l-log 2<=j*y+log y<=L+l. The floor-comparable index then gives M/2<=y<=4*M and L-log 2<=j*y<=L+l. All index and clock assumptions are explicit.

Exact source telescope (D5-compiled): ∀ {j : ℕ} (hj : 3 ≤ j) {X M ρ : ℝ}     (hXpos : 1 < X) (hX : 4 ≤ log X) (hM : 2 ≤ M) (hρ : 2 ≤ ρ)     (hroot : beta j ρ = referencePrice X)     (hjlo : log X / (2 * M) ≤ (j : ℝ))     (hjhi : (j : ℝ) ≤ log X / M),     X * log X / 2 ≤ ρ ^ j * log ρ ∧ ρ ^ j * log ρ ≤ X * log X ∧       log X + log (log X) - log 2 ≤ (j : ℝ) * log ρ + log (log ρ) ∧       (j : ℝ) * log ρ + log (log ρ) ≤ log X + log (log X) ∧       M / 2 ≤ log ρ ∧ log ρ ≤ 4 * M ∧       log X - log 2 ≤ (j : ℝ) * log ρ ∧       (j : ℝ) * log ρ ≤ log X + log (log X)

**Theorem 1.5 (growing_layer_floor_bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_floor_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_floor_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive L, M>=1 and L/M>=6, the natural floor is at least 3 and lies between L/(2*M) and L/M, with upper bound L. This is exact floor arithmetic, not a fixed-index limit.

Exact source telescope (D5-compiled): ∀ {L M : ℝ} (hL : 0 < L) (hM : 1 ≤ M)     (hlarge : 6 ≤ L / M),     3 ≤ ⌊L / M⌋₊ ∧ L / (2 * M) ≤ (⌊L / M⌋₊ : ℝ) ∧       (⌊L / M⌋₊ : ℝ) ≤ L / M ∧ (⌊L / M⌋₊ : ℝ) ≤ L

**Theorem 1.6 (quantitative_theta_error).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_theta_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_theta_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses the exact canonical MediumPNT psi error with exponent 1/10 and the exact psi-minus-theta O(sqrt) supplier once. Weakens c to c1=c/2, absorbs sqrt using log(t)^(-9/10), and fixes A>=1,Y0>1 before all endpoints.

Exact source telescope (D5-compiled): ∃ c1 A Y0 : ℝ,     0 < c1 ∧ 1 ≤ A ∧ 1 < Y0 ∧ ∀ t : ℝ, Y0 ≤ t →       |Chebyshev.theta t - t| ≤ A * t * exp (-c1 * log t ^ (1 / 10 : ℝ))

**Theorem 1.7 (root_pnt_suppression).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.root_pnt_suppression`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.root_pnt_suppression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose A0=max(1,12/c1). The slightly larger harmless constant gives c1*A0>=12. From y>=(A0*log L)^10/2 obtain c1*y^(1/10)>=6*log L, hence exp(-c1*y^(1/10))<=L^-6.

Exact source telescope (D5-compiled): ∀ {c1 A0 L y : ℝ} (hc : 0 < c1)     (hA : 1 ≤ A0) (hL : 1 < L) (hlarge : 12 ≤ c1 * A0)     (hy : (A0 * log L) ^ 10 / 2 ≤ y),     exp (-c1 * y ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6

**Theorem 1.8 (quantitative_moving_prime_roster).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_moving_prime_roster`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_moving_prime_roster` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constants come directly from quantitative_theta_error before L,rho,j. Endpoint errors at the ACTUAL rho and b=rho*(1+1/j^2) give theta(b)-theta(rho)>=rho/(2*j^2). The actual half-open prime interval is a finite difference of primesLE floors. Counting its logmass gives at least 2*j+2 distinct primes. No fixed-cardinality asymptotic window is reused. The explicit endpoint conditions are discharged in eventual_growing_roster.

Exact source telescope (D5-compiled): ∃ c A Y0 : ℝ,     0 < c ∧ 1 ≤ A ∧ 1 < Y0 ∧     ∀ (L ρ : ℝ) (j : ℕ), 3 ≤ j → 4 ≤ L → 2 ≤ ρ → Y0 ≤ ρ →       (j : ℝ) ≤ L → 6 * A ≤ L ^ 4 → L ^ 6 ≤ ρ →       log (ρ * (1 + 1 / (j : ℝ) ^ 2)) ≤ L →       exp (-c * log ρ ^ (1 / 10 : ℝ)) ≤ 1 / L ^ 6 →       ρ / (2 * (j : ℝ) ^ 2) ≤         Chebyshev.theta (ρ * (1 + 1 / (j : ℝ) ^ 2)) - Chebyshev.theta ρ ∧       ∃ S : Finset ℕ, S.card = 2 * j + 2 ∧         ∀ p ∈ S, p.Prime ∧ ρ < (p : ℝ) ∧           (p : ℝ) ≤ ρ * (1 + 1 / (j : ℝ) ^ 2)

**Theorem 1.9 (finite_roster_quantitative_repair).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.finite_roster_quantitative_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.finite_roster_quantitative_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuses finite_pack and insert_roster through a modifier-only unapplied patch. A maximal feasible finite subset has actual new slack below 2*log X/J. The returned natural k=b.k*product A has the same first support and exact factorization at EVERY natural p. Complete objective telescoping gives the exact full residual sum. Cost is bounded by 6/(X*J). No actual exponent of an original record is capped at J. Non-strict feasibility includes empty selection and exact partial-mass ties; delta=0 permits only the empty selection because all prime logweights are positive.

Exact source telescope (D5-compiled): ∀ {X : ℝ} (hX : 14 ≤ X)     {b : Budget} (hb : b.spec X) {J : ℕ} (hJ : 3 ≤ J) (S : Finset ℕ)     (hfull : log (2 * X) < ∑ p ∈ S, log p)     (hS : ∀ p ∈ S, p.Prime ∧ p ≤ b.Q ∧       log p ≤ 2 * log X / (J : ℝ) ∧       b.k.factorization p = J - 1 ∧       goldenLayerMarginal p J < referencePrice X ∧       referencePrice X - goldenLayerMarginal p J ≤ (2 / (J : ℝ)) * referencePrice X),     ∃ (k : ℕ) (A : Finset ℕ), A ⊆ S ∧       2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧       k = b.k * ∏ p ∈ A, p ∧       (∀ p : ℕ, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧       log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧       0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧       log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧       0 ≤ X - log (k : ℝ) ∧ X - log (k : ℝ) < 2 * log X / (J : ℝ) ∧       actualDefect X k - completeFirstLayerLoss X k =         ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p ∧       0 ≤ actualDefect X k - completeFirstLayerLoss X k +         referencePrice X * (X - log (k : ℝ)) ∧       actualDefect X k - completeFirstLayerLoss X k +         referencePrice X * (X - log (k : ℝ)) ≤ 6 / (X * (J : ℝ))

**Theorem 1.10 (original_price_exact_slack).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.original_price_exact_slack`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.original_price_exact_slack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuses the exact two_price_compare helper, whose k=m branch uses reflexivity. Expanding objectives retains mu*(X-log k) on the left. Complete first-layer prefix cancellation keeps ORIGINAL b.delta in |b.h+b.delta-H(m)|. There is no sign assumption on lambda-mu, no price lower bound and no replacement of all positive strict predecessors.

Exact source telescope (D5-compiled): ∀ {X μ : ℝ} (hX : 14 ≤ X) {m k : ℕ}     (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ)) (b : Budget) (hb : b.spec X)     (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))     (hkprefix : k.primeFactors = Nat.primesLE b.Q)     (hslack : 0 ≤ X - log (k : ℝ)),     k ≤ m ∧ actualDefect X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤       actualDefect X k - completeFirstLayerLoss X k + referencePrice X * (X - log (k : ℝ)) +         6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *           |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /             (X ^ 2 * log (X / 2))

**Theorem 1.11 (growing_layer_cost_conversion).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_cost_conversion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_cost_conversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual floor error, not eta substituted into the fixed-J theorem, converts 6/(X*J) to 12*A0^10*(loglog X)^10/(X*log X).

Exact source telescope (D5-compiled): ∀ {X A0 : ℝ} (hX : 1 < X)     (hA : 0 < A0) (hloglog : 0 < log (log X))     (hlarge : 6 ≤ log X / (A0 * log (log X)) ^ 10),     6 / (X * (⌊log X / (A0 * log (log X)) ^ 10⌋₊ : ℝ)) ≤       (12 * A0 ^ 10) * log (log X) ^ 10 / (X * log X)

**Theorem 1.12 (actual_higher_layer_quantitative_budget_repair).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_higher_layer_quantitative_budget_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_higher_layer_quantitative_budget_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The private by-body eventual_growing_roster chooses A0 once and J=floor(log X/(A0*loglog X)^10), proves root existence, all geometric/logarithmic bounds, exponential suppression, quantitative distinct prime supply, q<X/2, exact strict reference exponent J-1, total roster surplus, and the individual logweight bound. The final actual integer proof reuses finite arithmetic, returns the exact complete-loss sum and EVERY valuation increment, and proves H(k)-b.h=log k-log b.k. C=12*A0^10 and X0>exp(exp 1) precede every real X and literal Budget. No window/repair/response/energy hypothesis occurs in the public telescope.

Exact source telescope (D5-compiled): ∃ C X0 A0 : ℝ, 0 < C ∧ exp (exp 1) < X0 ∧ 1 ≤ A0 ∧     ∀ X : ℝ, X0 ≤ X → ∀ b : Budget, b.spec X →     ∃ k : ℕ, 2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧       0 ≤ X - log (k : ℝ) ∧       0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧       log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧       log (higherCore k : ℝ) - b.h = log (k : ℝ) - log (b.k : ℝ) ∧       0 ≤ actualDefect X k - completeFirstLayerLoss X k +         referencePrice X * (X - log (k : ℝ)) ∧       actualDefect X k - completeFirstLayerLoss X k +         referencePrice X * (X - log (k : ℝ)) ≤           C * log (log X) ^ 10 / (X * log X) ∧       let J := ⌊log X / (A0 * log (log X)) ^ 10⌋₊       ∃ A : Finset ℕ, 3 ≤ J ∧         (∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧           b.k.factorization p = J - 1 ∧           optimalLayerCount (referencePrice X) p = J - 1) ∧         k = b.k * ∏ p ∈ A, p ∧         log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧         (∀ p : ℕ, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧         actualDefect X k - completeFirstLayerLoss X k =           ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p

**Theorem 1.13 (actual_record_quantitative_repaired_prefix_residual).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_record_quantitative_repaired_prefix_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_record_quantitative_repaired_prefix_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A comap over the entire subtype of original (m,mu) pairs fixes one threshold before ALL m>=2 and arbitrary mu>0. Uses the literal Budget/spec, canonical_budget_eventually, original_record_bounds, and complete_first_layer_prefix_cancellation. The witness k<=m retains ACTUAL new slack in R_X(m)+mu*(X-log k), with ORIGINAL b.delta in the theta block. The reused comparison explicitly covers k=m by reflexivity; arbitrary actual exponents and every j>=2 remain in the full loss. No energy corollary is added.

Exact source telescope (D5-compiled): ∃ C X0 : ℝ, 0 < C ∧ exp (exp 1) < X0 ∧     ∀ m : ℕ, 2 ≤ m → ∀ μ : ℝ, 0 < μ →       (∀ a : ℕ, 0 < a → a < m →         goldenResourceObjective μ a < goldenResourceObjective μ m) →       X0 ≤ log (m : ℝ) →       ∃ (b : Budget) (k : ℕ), b.spec (log (m : ℝ)) ∧ 2 ≤ k ∧ k ≤ m ∧         k.primeFactors = Nat.primesLE b.Q ∧         0 ≤ log (m : ℝ) - log (k : ℝ) ∧         0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧         log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧         actualDefect (log (m : ℝ)) m - completeFirstLayerLoss (log (m : ℝ)) m +           μ * (log (m : ℝ) - log (k : ℝ)) ≤           C * log (log (log (m : ℝ))) ^ 10 / (log (m : ℝ) * log (log (m : ℝ))) +           6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *             |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /               ((log (m : ℝ)) ^ 2 * log (log (m : ℝ) / 2))

**Theorem 1.14 (finite_pack_exposure).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.finite_pack`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.finite_pack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existing completed helper, exact private-modifier removal only. Its original full telescope and proof body are unchanged. Actual consumers: finite_roster_quantitative_repair finite maximal selection.

Exact source telescope (D5-compiled): ∀ (S : Finset ℕ) (w : ℕ → ℝ) {d M : ℝ}     (hd : 0 ≤ d) (hfull : d < ∑ p ∈ S, w p)     (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ M),     ∃ A : Finset ℕ, A ⊆ S ∧ (∑ p ∈ A, w p) ≤ d ∧       0 ≤ d - ∑ p ∈ A, w p ∧ d - ∑ p ∈ A, w p < M

**Theorem 1.15 (insert_roster_exposure).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existing completed helper, exact private-modifier removal only. Its original full telescope and proof body are unchanged. Actual consumers: finite_roster_quantitative_repair exact factorization, support and complete loss identity.

Exact source telescope (D5-compiled): ∀ {X : ℝ} (hX : 4 < X) {b : Budget} (hb : b.spec X)     {J : ℕ} (hJ : 3 ≤ J) (A : Finset ℕ)     (hA : ∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧ b.k.factorization p = J - 1),     let k := b.k * ∏ p ∈ A, p     2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧       log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧       (∀ p, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧       actualDefect X k - completeFirstLayerLoss X k =         ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p

**Theorem 1.16 (two_price_compare_exposure).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existing completed helper, exact private-modifier removal only. Its original full telescope and proof body are unchanged. Actual consumers: original_price_exact_slack with the actual new slack and literal k=m reflexivity.

Exact source telescope (D5-compiled): ∀ {X μ : ℝ} {m k : ℕ}     (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ)) (hslack : 0 ≤ X - log (k : ℝ)),     k ≤ m ∧ actualDefect X m - actualDefect X k ≤       (referencePrice X - μ) * (X - log (k : ℝ))

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.finite_pack`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_higher_layer_quantitative_budget_repair`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.actual_record_quantitative_repaired_prefix_residual`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.adjacent_layer_strict`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.finite_roster_quantitative_repair`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_cost_conversion`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.growing_layer_floor_bounds`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.moving_interval_marginals`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.original_price_exact_slack`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_moving_prime_roster`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.quantitative_theta_error`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.root_pnt_suppression`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_beta_and_slope`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerQuantitativeBudgetRepair.uniform_root_geometry`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair](ActualHigherLayerBudgetRepair.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope](HigherLayerLogSlope.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
