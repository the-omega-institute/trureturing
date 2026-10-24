# Finite Prediction and Invariant Covers

## Abstract

Finite predictors correspond to invariant covers with bounded future diameter.

**Definition 1.1 (A finite predictor for every future word).**

Lean statement: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFinitePredictor`

*Formalization.* `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFinitePredictor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X be a nonempty set of actual states, A an arbitrary action alphabet, F a total deterministic action on X, and o an observation in a metric space Y. A predictor has a nonempty finite set S with at most s states, an initialization e from X to S, transitions G indexed by A, and an output h in Y. For every initial state x and every finite word w, including the empty word, the distance between h applied to G along w from e(x) and o applied to F along w from x is at most the nonnegative error epsilon. Words act from left to right. Transitions receive only the action and current machine state; output depends only on that state. Initialization need not commute with transitions.

**Definition 1.2 (A deterministic invariant cover).**

Lean statement: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.IsInvariantCover`

*Formalization.* `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.IsInvariantCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each set C(i) is nonempty, and every point of X belongs to at least one C(i). The sets may overlap. For every action a and index i, a single successor delta(a,i) satisfies F(a)[C(i)] contained in C(delta(a,i)). A center y(i) in Y bounds the supremum of the distances from o(x) to y(i), for x in C(i), by epsilon. This supremum is taken in the nonnegative extended reals, so no boundedness assumption is needed to define it.

**Definition 1.3 (A cover with a finite state budget).**

Lean statement: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFiniteInvariantCover`

*Formalization.* `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFiniteInvariantCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index set is nonempty and finite, with cardinality at most s. No finiteness, topology, or continuity assumption is imposed on X or A.

**Definition 1.4 (Distance over the full future).**

Lean statement: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.futureDistance`

*Formalization.* `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.futureDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The future distance of x and x-prime is the supremum, over all finite words w, of the distance between their observations after applying the same word. Its value lies in the nonnegative extended reals and can be infinite.

**Theorem 1.5 (Equivalence and the diameter of every cover member).**

Lean statement: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative epsilon and every integer state budget s at least one, a full-future predictor with at most s states exists if and only if a deterministic invariant cover with at most s nonempty members exists. For every invariant cover, any two points in the same member have future distance at most twice epsilon. This last assertion holds even for an infinite index set.

From a predictor, collect in C(i) all true states reached by any initial state and any word whose corresponding machine state is i. Remove unreachable machine states. The empty word gives a cover, appending an action gives a deterministic successor, and the prediction guarantee bounds every member around the machine output.

Conversely, choose for each true initial state a member containing it. Induction on words keeps the true state in the member named by the machine. The radius bound then proves prediction accuracy. Two points in one member remain in a common successor member after every word. The triangle inequality through its center bounds each pair of observations by twice epsilon, and taking the supremum proves the diameter bound. The construction asserts existence and does not assert effective computability.

Application (§§9.1–9.2): irrational rotation, finite external-time codes, and the sharp autonomous obstruction. Let Phase = AddCircle(1) = ℝ/ℤ, with [t] denoting the class of t, and let o : Phase → ℂ be AddCircle.toCircle viewed in the complex plane. For every real α define Rα(x) = x + [α] and Rαⁿ(x) = x + n • [α], for every n ∈ ℕ including zero. The action alphabet is Unit and F((),x) = Rα(x). Thus runWord F w x = Rα^{length(w)}(x); every natural time occurs as the length of a word. Distances below are complex chordal distances, ‖z − z′‖. Their extended-real versions are edist(z,z′) = ENNReal.ofReal(‖z − z′‖); all displayed suprema of edist take values in ENNReal.

Definition 9.1: the finite-horizon minimum. For every real α, every H ∈ ℕ, including H = 0, and every ε > 0, set S_{H,ε}(α) = autonomousStateCount Rα o H ε. This number is positive and is the least element of {s ∈ ℕ | HasFiniteHorizonPredictor F o H ε s}. It is attained: there are a nonempty finite type S with |S| = S_{H,ε}(α), an initialization e : Phase → S, an autonomous update G : S → S, and a complex readout h : S → ℂ such that ‖h(Gⁿ(e(x))) − o(Rαⁿ(x))‖ ≤ ε for every phase x and every natural n ≤ H. The existing autonomous_prediction_entropy theorem supplies existence, positivity, leastness, and this exact-cardinality witness for continuous dynamics and observation on a nonempty compact space. Here Phase is compact, Rα is continuous by addition, and o is continuous by AddCircle.continuous_toCircle followed by the inclusion Circle → ℂ. The Unit-word identity above identifies the theorem's finite-horizon predicate with all times 0 ≤ n ≤ H, with the same α and complex output metric. Thus the minimum in Definition 9.1 is the existing autonomous state count; this finite-horizon conclusion holds for all real α.

(1) Literal exponential observation. For every t ∈ ℝ, o([t]) = Complex.exp((2πt) · Complex.I). In particular, ‖o(x)‖ = 1 for every phase x, and o(x+y) = o(x)o(y). These identities follow from AddCircle.toCircle_apply_mk at period 1, Circle.coe_exp, AddCircle.toCircle_add, and Circle.norm_coe. At phase zero the same parameter α gives o(Rαⁿ(0)) = exp(2πi nα) for every n ∈ ℕ: n • [α] = [nα], and the two exponent expressions agree by multiplication in ℂ. This is a literal observation identity with the same α throughout. The circle phase norm is ‖[t]‖ = |t − round(t)|, and |t − round(t)| ≤ |t − k| for every integer k; hence it is precisely the nearest-integer quantity ‖t‖_𝕋 = min_{k ∈ ℤ}|t − k| used in Definition 9.1.

(2) Full-future chordal metric. For every real α, every x,y ∈ Phase, and every n ∈ ℕ, o(Rαⁿ(x)) − o(Rαⁿ(y)) = (o(x) − o(y))o(n • [α]). The last factor has norm one, so the norm of this difference equals ‖o(x) − o(y)‖. Consequently futureDistance F o x y = sup_{w : List Unit} edist(o(runWord F w x),o(runWord F w y)) = ENNReal.ofReal(‖o(x) − o(y)‖). This includes the empty word and the entire unbounded future, for all real α; irrationality is unnecessary here.

(3) Quantitative nearest-grid code with an external time argument. For every real α and every ε > 0, choose M ∈ ℕ with M > 0 and M ≥ π/ε, and take C = Fin M. Write g(j) = [j/M]. For each phase x, choose e(x) ∈ Fin M minimizing ‖x − g(j)‖ over all labels j. This finite minimum exists, and any nearest label may be chosen in a tie. To bound the minimum, lift x to t ∈ [0,1), put k = round(Mt), and reduce k modulo M to obtain a label j. Since [k/M] = [j/M], the quotient norm and the rounding estimate give ‖x − g(j)‖ ≤ |t − k/M| = |Mt − round(Mt)|/M ≤ 1/(2M). Nearestness gives the same bound for e(x), including wraparound at phase zero.

Define the literal decoder D(j,n) = exp(2πi(j/M + nα)) for j ∈ Fin M and n ∈ ℕ. The circle chord satisfies ‖o(x) − o(y)‖ ≤ 2π‖x − y‖: choose a centered lift u ∈ [−1/2,1/2) of x − y, so |u| = ‖x − y‖, factor out the unit complex number o(y), and apply |exp(2πiu) − 1| ≤ 2π|u|. Clause (2) then yields ‖D(e(x),n) − o(Rαⁿ(x))‖ ≤ 2π‖x − g(e(x))‖ ≤ π/M ≤ ε for every phase x and every natural query n, including zero. The encoder is specified by choice of a finite minimum. The finite label count bounds the stored labels; n is an external decoder input, and the decoder's computational resources are unrestricted.

(4) Every positive-period subsequence and every complex center. If α ∈ ℝ is irrational, then for every x ∈ Phase, every μ,p ∈ ℕ with p > 0, and every c ∈ ℂ, sup_{k ∈ ℕ} edist(o(Rα^{μ+kp}(x)),c) = ENNReal.ofReal(1 + ‖c‖). Indeed pα is irrational by Irrational.natCast_mul. AddCircle.denseRange_zsmul_coe_iff at period 1 gives density of its integer multiples in Phase; denseRange_zsmul_iff_nsmul gives density of its natural multiples in this compact additive group. Translation by x + μ • [α] and the homeomorphism AddCircle.homeomorphCircle at period 1 carry that dense range to k ↦ o(Rα^{μ+kp}(x)) in Circle. The offset and period here are arbitrary subject only to μ ∈ ℕ and p ∈ ℕ, p > 0.

To obtain the exact supremum in (4), the triangle inequality gives ‖z − c‖ ≤ 1 + ‖c‖ for every unit complex z. If c = 0, every such z has distance 1. If c ≠ 0, the unit point z* = −(1/‖c‖)c satisfies ‖z* − c‖ = 1 + ‖c‖. Let M be the extended supremum along the dense subsequence. The set of z in Circle satisfying edist(z,c) ≤ M is closed by continuity and contains the dense range, hence contains z*. It follows that ENNReal.ofReal(1 + ‖c‖) ≤ M, giving equality with the upper bound. The supremum need not be achieved at a particular subsequence time. No restriction on the modulus of c is imposed. The same bound proves boundedness of the real errors, and continuity on the dense range gives sup_{k ∈ ℕ} ‖o(Rα^{μ+kp}(x)) − c‖ = sup_{|z|=1} ‖z − c‖ = 1 + ‖c‖ as well. For these bounded nonnegative errors, the extended supremum is ENNReal.ofReal of the real supremum.

(5) Obstruction for every autonomous finite machine. Fix any irrational α, any x ∈ Phase, any finite type S, any total map G : S → S, any readout h : S → ℂ, and any initial state q ∈ S. Define E(α,x,G,h,q) = sup_{n ∈ ℕ} edist(h(Gⁿ(q)),o(Rαⁿ(x))). The supplied q makes S nonempty. The finite-orbit theorem finite_orbit_and_readout_eventually_periodic supplies μ,p ∈ ℕ for this very G,h,q with 0 < p and μ+p ≤ |S|, such that for every t ≥ μ both G^{t+p}(q) = Gᵗ(q) and h(G^{t+p}(q)) = h(Gᵗ(q)). Iterating this tail equality gives h(G^{μ+kp}(q)) = c for every k ∈ ℕ, where c = h(G^μ(q)) is the actual readout of this machine at μ.

Apply (4) using precisely that μ, p, and c, with the original α and x. The same machine therefore satisfies E(α,x,G,h,q) ≥ sup_{k ∈ ℕ} edist(h(G^{μ+kp}(q)),o(Rα^{μ+kp}(x))) = ENNReal.ofReal(1 + ‖h(G^μ(q))‖) ≥ 1. The first inequality is restriction of the all-time supremum to those times; symmetry of edist identifies the restricted errors with (4). Thus E ≥ 1 for every finite S, G, arbitrary complex h, and q, for every initial phase x. This argument uses no bound or unit-circle assumption on the machine readout. A clock or a fresh observation is not an input to G or h.

(6) Sharp attainment by one state. For every real α and every x ∈ Phase, take S = Unit, G = id, h(()) = 0, and q = (). At every natural time the error is ‖0 − o(Rαⁿ(x))‖ = 1, so E(α,x,id,0,()) = 1 exactly. Combined with (5), this is the attained optimal all-time error over autonomous finite machines when α is irrational. The attainment statement itself does not require irrationality.

(7) No finite predictor or deterministic invariant cover below error one. For every irrational α, every real ε < 1, and every natural state budget s, both HasFinitePredictor F o ε s and HasFiniteInvariantCover F o ε s are false. A proposed predictor would have a nonempty finite S with |S| ≤ s, initialization e : Phase → S, transition G : Unit → S → S, and readout h : S → ℂ, satisfying the metric error bound for every phase and every finite word, including the empty word. Fix a phase x, and use w = List.replicate n (). The state is (G ())ⁿ(e(x)), so the real error ‖h((G ())ⁿ(e(x))) − o(Rαⁿ(x))‖ is at most ε for every n. The errors are bounded above since the machine has finite readout range and the true output has norm one. Their real supremum is therefore at most ε, whereas (5) makes it at least one, a contradiction. This argument covers negative ε directly in the metric norm and every s, including zero.

A qualifying cover has a nonempty finite index type I with |I| ≤ s, nonempty sets C(i) covering Phase, a deterministic successor δ : Unit → I → I, and centers y : I → ℂ. It must satisfy Rα[C(i)] ⊆ C(δ((),i)) and sup_{x ∈ C(i)} edist(o(x),y(i)) ≤ ENNReal.ofReal(ε) for every i; members may overlap. Nonemptiness of I forces 1 ≤ s. Put ε′ = max(ε,0), so 0 ≤ ε′ < 1. Monotonicity of ENNReal.ofReal preserves all radius bounds when ε is replaced by ε′. The existing finite_predictor_iff_forward_invariant_cover now applies at ε′ and s: Phase is nonempty, ℂ is a metric space, F is total, ε′ ≥ 0, and s ≥ 1. Choosing an initial containing member and following δ would produce the forbidden predictor at ε′. This proves cover exclusion for every real ε < 1 and every natural s without applying the equivalence at a negative error or a zero budget. Conversely, the general equivalence obtains cover members from all reachable pairs of true and machine states and removes empty members, as described above. Its additional conclusion bounds every member's full-future diameter by ENNReal.ofReal(2ε′), even for an infinite index set. A finite cover by small static balls alone does not supply the deterministic successor condition.

The finite external-time code in (3) and the autonomous obstruction in (5) concern different access to time. In (3), n enters the decoder directly; in (5), every time dependence must pass through iteration of a finite state. Clauses (1), (2), (3), and (6) hold for every real α. The density, machine obstruction, and cover exclusion in (4), (5), and (7) require irrational α. At ε = 1 the zero-output machine attains the threshold, and the single cover member Phase with center 0 and its own successor also has radius 1. These are statements about exact real and complex objects, with no physical precision or resource equivalence asserted.

Reused repository sources. At the-omega-institute/trureturing revision b9295ac6746476e54f67337977be4af1b154f778, the finite-period witness is D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic in D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean. The word convention is runWord in D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean; its autonomous specialization is run_unit_word in D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality.lean. The predictor, cover, and full-future definitions and their equivalence are HasFinitePredictor, IsInvariantCover, HasFiniteInvariantCover, futureDistance, and finite_predictor_iff_forward_invariant_cover in namespace D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover, in the correspondingly named .lean module. They are instantiated with X = Phase, A = Unit, Y = ℂ, F((),x) = x + [α], and o as above.

The finite-horizon predicate HasFiniteHorizonPredictor belongs to D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.lean, in namespace D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw. The definition autonomousStateCount and the public theorem autonomous_prediction_entropy belong to D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy.lean, in namespace D5.S3.Observer.MetricGeometry.AutonomousPredictionEntropy. Their finite-horizon minimum and attainment conclusions give Definition 9.1 with exactly the original phases, natural times, autonomous machine, and arbitrary complex readout.

Pinned Mathlib sources (Lean 4.35.0, Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679). Mathlib/Analysis/Normed/Group/AddCircle.lean supplies UnitAddCircle.norm_eq and AddCircle.norm_coe_eq_abs_iff; Mathlib/Algebra/Order/Round.lean supplies round_le and abs_sub_round. Mathlib/Topology/Instances/AddCircle/Defs.lean supplies AddCircle.equivIco, AddCircle.coe_equivIco, and AddCircle.nsmul_eq_zero_iff; Mathlib/Data/Fintype/Lattice.lean supplies Finite.exists_min for the nearest label. Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean supplies AddCircle.toCircle_apply_mk, AddCircle.toCircle_add, AddCircle.continuous_toCircle, AddCircle.homeomorphCircle and AddCircle.homeomorphCircle_apply; Mathlib/Analysis/Complex/Circle.lean supplies Circle.coe_exp and Circle.norm_coe. The chord estimate uses Real.norm_exp_I_mul_ofReal_sub_one_le from Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean. Mathlib/NumberTheory/Real/Irrational.lean supplies Irrational.natCast_mul, and Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean supplies AddCircle.denseRange_zsmul_coe_iff. In Mathlib/Topology/Algebra/Group/SubmonoidClosure.lean, denseRange_zsmul_iff_nsmul is the additive form generated from denseRange_zpow_iff_pow by to_additive. Mathlib/Topology/Order/OrderClosed.lean supplies le_on_closure, which extends the bounded real error inequality from the dense range to Circle; the supremum conversion uses ENNReal.toReal_iSup. These APIs supply rounding, finite choice, the chord estimate, and density; the remaining calculations use unit norm, the triangle inequality, and restriction of a supremum.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFiniteInvariantCover`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFinitePredictor`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.IsInvariantCover`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.finite_predictor_iff_forward_invariant_cover`
- Truth anchor: `D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.futureDistance`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
