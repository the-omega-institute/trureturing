# Literal complete higher loss controls every actual higher mass

## Abstract

Literal complete higher loss controls every actual higher mass.

For every real X>=exp(2) and every natural n>=1, R is literally actualDefect(X,n)-completeFirstLayerLoss(X,n). The common finite dual set includes coordinates(n) and the entire low-price canonical inventory. The exact all-support identity and both dual signs yield Delta<=R X log X/s+400s sqrt X log X+400log^2 X. For R>0 the source chooses precisely s=min(1/2,sqrt(R sqrt X)). For R=0 an actual epsilon argument proves the discrete 400log^2 X remainder without any continuity of strict inventory or exclusion of ties. These steps yield constant 1000 with no record premise, exponent cap, response assumption, RH or PNT estimate on the finite proof path.

The complete inventory application uses A(n)=coordinates(n), containing every pair (p,j) with p prime and 2<=j<=v_p(n), where v_p(n)=n.factorization(p). Put lambda=referencePrice(X)=1/(X log X) and C(X)=coordinates(strictInteger(lambda)). Define M(X,n) as the sum of log(p) over (A(n) minus C(X)) union (C(X) minus A(n)). Every missing or excess higher coordinate contributes its positive logarithmic prime weight before summation, with no cancellation between coordinates.

For every real X>=exp(2) and every natural n>=1, put R=actualDefect(X,n)-completeFirstLayerLoss(X,n). The full application gives 0<=R and M(X,n)<=1000*(X^(3/4)*log(X)*sqrt(R)+X*log(X)*R+log(X)^2), with 3/4 a real exponent. Nonnegativity of R is the first component of ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity. The inventory bound is an application of frozen library results, not a new theorem or a claim of literature novelty.

To obtain the L1 estimate, apply CompleteHigherInventoryDuality.finite_dual_abs separately on each singleton {c}, with an occupied Boolean i(c), gain b(c) and nonnegative weight w(c). Its absolute mass difference is exactly the weight of the mismatch between i(c) and the strict predicate 0<b(c)-lambda*w(c). This equality includes w(c)=0 and central threshold ties. Sum these singleton inequalities over an arbitrary finite S, including empty S. With F(eta)=sum over S of max(b(c)-eta*w(c),0), h(eta)=sum over S of w(c) on that strict predicate, H=sum over occupied coordinates of w(c), B=sum over occupied coordinates of b(c), and R_S=F(lambda)-B+lambda*H, finite-sum normalization gives the full weighted mismatch <=R_S/t+h(lambda-t)-h(lambda+t) for t>0. The same R_S/t and neighbouring strict masses are retained; taking the absolute value only after summation would discard coordinate information.

For the arithmetic application take 0<s<=1/2, t=s*lambda, b=CompleteHigherInventoryDuality.coordinateGain, w=CompleteHigherInventoryDuality.coordinateWeight and i(c)=decide(c in coordinates(n)). Use S=coordinates(n) union coordinates(strictInteger(lambda-t)); it independently includes ALL actual prime supports and all exponents 2<=j<=v_p(n). CompleteHigherInventoryDuality.canonical_coordinates_antitone puts the central and both neighbouring canonical coordinate sets inside S. CompleteHigherInventoryDuality.mem_coordinates, canonical_mem and positive_coordinate identify the strict central predicate with C(X), so the finite mismatch sum is exactly M(X,n). higherMass_eq_coordinate_sum identifies H, inventoryGain identifies B, and strictMass_eq identifies both neighbouring masses. CompleteHigherInventoryDuality.literal_loss_identity identifies R_S with precisely R. The low-price canonical set bounds only canonical occupancy and places no support or exponent cap on n.

ActualHigherMassResponse.actual_higher_mass_response then gives M(X,n)<=R*X*log(X)/s+400*s*sqrt(X)*log(X)+400*log(X)^2 for every 0<s<=1/2. Applying ActualHigherMassCoercivity.balance_response with Delta=M(X,n), q=sqrt(X) and L=log(X), and using sqrt(X)*sqrt(sqrt(X))=X^(3/4), gives the stated constant-1000 bound. This derivation is singleton reuse, finite-sum normalization and application of the existing all-support loss identity and response and balancing estimates; it does not add a separately named inventory theorem.

The R=0 branch of balance_response retains the discrete logarithmic boundary remainder through its epsilon argument. Zero loss does not force M(X,n)=0: coordinates at a central tie are excluded by the strict canonical threshold and may be actually occupied with zero loss. The unit n=1, empty higher inventories, valuations zero and one, arbitrary higher layers and all actual prime supports stay in scope. No record hypothesis, PNT estimate or response assumption is added. The application establishes no prescribed-bank payment, signed B(P) bound, Robin inequality beyond 5040 or proof of RH.

**Theorem 1.1 (actual dual estimate).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_dual_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_dual_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem actual_dual_estimate {X s : ℝ} (hX : exp 2 ≤ X) {n : ℕ} (hn : 1 ≤ n) (hs : 0 < s) (hs2 : s ≤ 1 / 2) : |higherMass n - higherMass (strictInteger (referencePrice X))| ≤ (actualDefect X n - completeFirstLayerLoss X n) * X * log X / s + 400 * s * sqrt X * log X + 400 * log X ^ 2

**Theorem 1.2 (balance response).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.balance_response`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.balance_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem balance_response {Δ R q L : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hL : 0 < L) (hbound : ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → Δ ≤ R * q ^ 2 * L / s + 400 * s * q * L + 400 * L ^ 2) : Δ ≤ 1000 * (q * sqrt q * L * sqrt R + q ^ 2 * L * R + L ^ 2)

**Theorem 1.3 (actual complete higher mass coercivity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean statement: theorem actual_complete_higher_mass_coercivity {X : ℝ} (hX : exp 2 ≤ X) (n : ℕ) (hn : 1 ≤ n) : let R := actualDefect X n - completeFirstLayerLoss X n; 0 ≤ R ∧ |higherMass n - higherMass (strictInteger (referencePrice X))| ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2)

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_dual_estimate`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.balance_response`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualHigherMassResponse](ActualHigherMassResponse.md)
