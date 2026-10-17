# Exact State and Bit Counts for the Binary Shift

## Abstract

At error in [0,1), binary shift prediction through time H requires exactly H plus one bits.

**Definition 1.1 (Prediction through a prescribed horizon).**

Lean statement: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.HasFiniteHorizonPredictor`

*Formalization.* `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.HasFiniteHorizonPredictor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a deterministic controlled system F with observation o in a metric space, a predictor with state budget s consists of a nonempty finite state set S of cardinality at most s, an initialization e, total deterministic transitions G, and a readout h. For every initial state x and every action word w of length at most H, the distance between the predicted and true outputs is at most epsilon. The empty word is included. Transitions receive only the current state and action; readout receives only the state. Neither receives the time or a new observation. The predictor may depend on H and epsilon.

## An autonomous rational clock on the circle

Fix any real rotation increment α, any integer p, any natural q > 0, and any natural horizon H. Let X = ℝ/ℤ, represented in Lean by UnitAddCircle, and let rep(x) be the unique representative t in [0,1). The true transition is F((),x) = x + α modulo one, with the singleton action alphabet Unit. Observe the complex phase o(x) = exp(2πit). This is independent of the chosen real lift of x because the exponential has period one in t.

Use the nonempty state set S = ℤ/qℤ, represented by ZMod q; it has exactly q elements (ZMod.card). Initialize once by e_q(x) = round(q rep(x)) modulo q. The total autonomous transition is G((),j) = j + p modulo q, and the readout is h(j) = exp(2πik/q), where k is any integer representing j. Changing k by a multiple of q leaves the readout unchanged; this is the standard character ZMod.stdAddChar, with its integer formula ZMod.stdAddChar_coe.

For every initial circle point x and every natural n, repeated addition gives G^n(e_q(x)) = e_q(x) + np modulo q. The true state is F^n(x) = x + nα modulo one, with output exp(2πi(t + nα)). The additive iteration identity is add_right_iterate_apply. These formulas hold for all n, including zero; only the uniform error estimate below restricts n to the horizon.

Write t = rep(x), r = round(qt), and u = r/q as real numbers. The nearest-integer bound abs_sub_round gives |r - qt| ≤ 1/2, hence |u - t| ≤ 1/(2q), since q is positive. The representative identity AddCircle.coe_equivIco and the quotient formula ZMod.toAddCircle_intCast identify the encoded circle point with u modulo one and x with t modulo one. Projection to the quotient does not increase the norm (QuotientAddGroup.norm_mk_le_norm), so the initial circle error is ‖ZMod.toAddCircle(e_q(x)) - x‖ ≤ 1/(2q). This also covers rounding across the seam at zero.

At time n choose the real lifts a_n = u + np/q for the predicted phase and b_n = t + nα for the actual phase. Their difference is (u - t) + n(p/q - α). The triangle inequality therefore gives |a_n - b_n| ≤ 1/(2q) + n|α - p/q|. For any real a,b, factoring out the unit complex number exp(2πib) and applying Real.norm_exp_I_mul_ofReal_sub_one_le at 2π(a-b) gives |exp(2πia) - exp(2πib)| ≤ 2π|a-b|. Combining the two estimates, for every x and every natural n ≤ H the complex output distance is at most π/q + 2πn|α - p/q| ≤ π/q + 2πH|α - p/q|.

In HasFiniteHorizonPredictor the parameters are X = UnitAddCircle, A = Unit, Y = ℂ with its usual metric, F and o as above, horizon H, error ε = π/q + 2πH|α - p/q|, and state budget s = q. The witness is S = ZMod q with initialization e_q, transition G and readout h. For a word w of length n, the recursive definition ControlledBehaviorUniversality.runWord applies exactly n copies of the single action. Induction on w gives runWord G w (e_q(x)) = e_q(x) + np and runWord F w x = x + nα in their respective quotients. Thus the displayed bound is precisely the required distance inequality for every w with length at most H. The empty word reads the initialized state. After initialization, neither transition nor readout receives time or a new observation; the same fixed clock works at every read time.

The cases H = 0 and q = 1 require no exception. At horizon zero the bound is π/q and includes the initial readout. At q = 1 the clock has one state, its transition is constant and its readout is 1; the same estimate applies. If α = p/q, the drift term vanishes and the error bound π/q holds for every natural time with this same clock.

The number q is the cardinality of this explicit construction and therefore an achievable state budget; no minimum-state or optimality assertion follows. This application gives no exact bit law, precision-complexity bound, computability guarantee or initialization, storage or running-cost bound. Initialization remains an arbitrary map of the real initial phase in the observational model; no physical implementation with finite precision is asserted. The binary-shift theorem below concerns a different system with real sign outputs and retains its exact minimum 2^(H+1) for 0 ≤ ε < 1. The clock estimate is an application of the stated rounding, quotient, iteration and chord bounds, with no claim of research novelty.

## The golden rotation: an attained minimum and its state-label bits

Fix φ = Real.goldenRatio = (1+√5)/2, α = φ⁻¹, 0 < ε < 1/2, and a natural horizon H, including zero. Use exactly the circle system and complex observation above. Write P(k) for HasFiniteHorizonPredictor F o H ε k. Thus P(k) asserts the existence of a nonempty finite carrier of cardinality at most k, a total initializer on all circle phases, a fixed autonomous transition, and a fixed readout into ℂ. Its accuracy requirement includes every Unit word of length at most H, including the empty word. The minimum below ranges over all these predictors, with no restriction to clocks or to unit-circle-valued readouts.

Put T = max{2, 2π/ε, √(4πH/ε)}. Choose the least index m with q = F_m ≥ T, and put p = F_(m−1). Such an index exists: choose a natural N ≥ T and use Nat.le_fib_self at N+5, where its hypothesis 5 ≤ N+5 holds. Since T ≥ 2, m ≥ 3. Minimality gives F_(m−1) < T, while Nat.fib_add_two and Nat.fib_mono give F_m ≤ 2F_(m−1). Consequently 0 < q < 2T. This uses the first crossing, rather than an arbitrary large Fibonacci denominator.

The absolute-defect clause of FibonacciNearReturn.fibonacci_near_return, at n=m with 1 ≤ m, gives |q/φ−p| = φ^(−m). Here fibonacciReturnDefect m is exactly q/φ−p. Real.goldenRatio_mul_fib_succ_add_fib at m−1 gives φq+p = φ^m; since φ>1, q>0 and p≥0, this is greater than q. Dividing the defect by q yields |α−p/q| = φ^(−m)/q < 1/q². Apply the preceding rational-clock construction with this actual integer p, positive natural q, α=φ⁻¹ and the same H. Since q≥2π/ε and q≥√(4πH/ε), its error is at most π/q + 2πH/q² ≤ ε/2 + ε/2 = ε. The drift comparison multiplies by the nonnegative quantity 2πH, so H=0 is included. Thus P(q) is established by an actual fixed clock, rather than assumed accuracy.

Feasibility now permits s = Nat.find (∃ k, P(k)). Nat.find_spec supplies P(s), and Nat.find_min' proves that s is at most every feasible budget. Extract its carrier S, initializer e, transition G and readout h. If r=|S|≤s, the identical witness proves P(r), hence minimality gives s≤r. Therefore |S|=s and s≥1. This cardinality bridge makes s an attained actual minimum, not a freely chosen state-count parameter. In particular s≤q<2T.

For the lower bound, use the public fourth clause of D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness.irrational_slope_faithfulness at the irrational slope φ. Its FinitePrecisionStable estimate separates integer labels with horizontal displacement at most the original positive integer q by more than 1/(√5 q+1). Set r=round(qα) and compare (q,−q−r) with (0,0). Since α=φ−1, their output gap is |qα−r| = ‖qα‖_𝕋 by UnitAddCircle.norm_eq. For q≥2, √5<5/2 implies √5 q+1<3q, so ‖qα‖_𝕋>1/(3q). For q=1 separately, 3/2<φ<5/3 and the centered lift α−1 give ‖α‖_𝕋=2−φ>1/3. Thus the bound holds for every positive original displacement q; no reduced rational denominator is substituted for it.

Apply ArithmeticHorizon.finite_predictor_horizon to the minimizing witness's actual map G(()) : S→S, readout h : S→ℂ, initial state e(0), phase x=0, α=φ⁻¹, error ε and horizon H. The supplier is the published ArithmeticHorizon.lean at revision b236bd0350b6accb372f59352fe7b079ac911a29 (https://github.com/the-omega-institute/trureturing/blob/b236bd0350b6accb372f59352fe7b079ac911a29/D5/S3/Observer/MetricGeometry/ArithmeticHorizon.lean). A Unit word consisting of n copies of () is exactly n iterations, so uniform word accuracy supplies its hypothesis for every n≤H, including n=0. With a=arcsin(ε)/π and c=1/3, ν=1, the separation estimate gives p/‖pα‖_𝕋≤3p²≤3s² for 1≤p≤s. Taking the finite maximum in the supplier's Ψ_α(s) and using |S|=s yields the strict bound H<s+3as². Together, the exact original bounds are H<s+3as² and s<2max{2,2π/ε,√(4πH/ε)}, for every natural H.

For H≥1 only, put K=1+3a and B=max{2,2π/ε,√(4π/ε)}. These positive constants depend only on ε. Since s≥1, s+3as²≤Ks²; the lower bound therefore gives √H/√K<s. Also √H≥1 and √(4πH/ε)=√(4π/ε)√H, so T≤B√H and s<2B√H. Hence (1/√K)√H<s<(2B)√H, with explicit positive constants and the same actual minimum for all H≥1. This is the fixed-ε square-root state law.

Let b=⌈log₂s⌉. The ceiling inequalities Int.le_ceil and Int.ceil_lt_add_one give 0≤b−log₂s<1; the lower gap may be zero. Strict monotonicity of Real.logb at base two, its product and quotient identities, and log₂√u=(1/2)log₂u for u>0 transform the two square-root bounds into −(1/2)log₂K < b−(1/2)log₂H < 1+log₂(2B). Both endpoints depend only on ε, proving the stated bounded additive error. These logarithms of H are used only for H≥1; the exact minimum and original inequalities already include H=0.

The bit count encodes only the current internal state label of the predictor in the stated observational model. Transition and output tables, real constants, initialization, computational cost and numerical precision are separate resources. The minimum is a mathematical existence result over arbitrary total initializers and complex readouts; no finite-precision physical realization or global research-priority claim follows. The binary-shift law below remains the exact law for its different system.

**Definition 1.2 (The leading bit as a sign).**

Lean statement: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binaryObservation`

*Formalization.* `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binaryObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual state is an infinite binary sequence indexed by the natural numbers. False represents zero and true represents one. The observation is minus one raised to the leading bit: zero gives one, and one gives minus one.

**Theorem 1.3 (The exact minimum state and bit counts).**

Lean statement: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binary_shift_exact_bit_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binary_shift_exact_bit_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be the left shift, so that coordinate j after one step is the old coordinate j plus one. For every natural horizon H and every real error epsilon with zero less than or equal to epsilon and epsilon less than one, the least achievable autonomous state budget is 2^(H+1). Its ceiling base-two logarithm, expressed by Nat.clog, is H+1. The action alphabet is a singleton, so the transitions are autonomous. Predictor outputs may be arbitrary real numbers. Both H equal to zero and epsilon equal to zero are included.

For the upper bound, store the first H+1 bits. Read the sign of the first bit, shift left at each step, and append zero. Induction on the number of steps shows that each remaining coordinate equals the corresponding original coordinate. Thus every readout through time H is exact, using 2^(H+1) states and no additional clock.

For the lower bound, extend every prefix of length H+1 by zeros. If two different prefixes had the same initialized state, their predicted outputs would coincide at a coordinate where their true signs differ. The true outputs there have distance two, while the triangle inequality bounds that distance by twice epsilon, which is strictly less than two. Initialization is therefore injective on all prefixes. Counting them gives the lower bound, and the ceiling logarithm of a power of two gives the exact bit count.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.HasFiniteHorizonPredictor`
- Truth anchor: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binaryObservation`
- Truth anchor: `D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binary_shift_exact_bit_law`
- Dependency: [D5/S3/Observer/MetricGeometry/ContractingDigitMemory](ContractingDigitMemory.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/DominanceMemoryUpdate](../../ObserverMemory/Trajectories/DominanceMemoryUpdate.md)
