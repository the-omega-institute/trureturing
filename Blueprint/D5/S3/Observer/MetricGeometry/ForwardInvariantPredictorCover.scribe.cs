using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class ForwardInvariantPredictorCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite predictors correspond to invariant covers with bounded future diameter.",
        H("Finite Prediction and Invariant Covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-future-predictor"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFinitePredictor"),
                H("A finite predictor for every future word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X be a nonempty set of actual states, A an arbitrary action alphabet, "
                    + "F a total deterministic action on X, and o an observation in a metric space Y. "
                    + "A predictor has a nonempty finite set S with at most s states, an initialization "
                    + "e from X to S, transitions G indexed by A, and an output h in Y. For every "
                    + "initial state x and every finite word w, including the empty word, the distance "
                    + "between h applied to G along w from e(x) and o applied to F along w from x "
                    + "is at most the nonnegative error epsilon. Words act from left to right. "
                    + "Transitions receive only the action and current machine state; output depends "
                    + "only on that state. Initialization need not commute with transitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("invariant-cover"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.IsInvariantCover"),
                H("A deterministic invariant cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each set C(i) is nonempty, and every point of X belongs to at least one C(i). "
                    + "The sets may overlap. For every action a and index i, a single successor "
                    + "delta(a,i) satisfies F(a)[C(i)] contained in C(delta(a,i)). A center y(i) in Y "
                    + "bounds the supremum of the distances from o(x) to y(i), for x in C(i), by "
                    + "epsilon. This supremum is taken in the nonnegative extended reals, so no "
                    + "boundedness assumption is needed to define it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-invariant-cover"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFiniteInvariantCover"),
                H("A cover with a finite state budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index set is nonempty and finite, with cardinality at most s. "
                    + "No finiteness, topology, or continuity assumption is imposed on X or A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("future-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.futureDistance"),
                H("Distance over the full future"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The future distance of x and x-prime is the supremum, over all finite words w, "
                    + "of the distance between their observations after applying the same word. "
                    + "Its value lies in the nonnegative extended reals and can be infinite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("predictor-cover-equivalence-and-diameter"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover."
                    + "finite_predictor_iff_forward_invariant_cover"),
                H("Equivalence and the diameter of every cover member"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative epsilon and every integer state budget s at least one, "
                        + "a full-future predictor with at most s states exists if and only if a "
                        + "deterministic invariant cover with at most s nonempty members exists. "
                        + "For every invariant cover, any two points in the same member have future "
                        + "distance at most twice epsilon. This last assertion holds even for an "
                        + "infinite index set.")),
                    Paragraph(Text(
                        "From a predictor, collect in C(i) all true states reached by any initial "
                        + "state and any word whose corresponding machine state is i. Remove "
                        + "unreachable machine states. The empty word gives a cover, appending an "
                        + "action gives a deterministic successor, and the prediction guarantee "
                        + "bounds every member around the machine output.")),
                    Paragraph(Text(
                        "Conversely, choose for each true initial state a member containing it. "
                        + "Induction on words keeps the true state in the member named by the machine. "
                        + "The radius bound then proves prediction accuracy. Two points in one member "
                        + "remain in a common successor member after every word. The triangle "
                        + "inequality through its center bounds each pair of observations by twice "
                        + "epsilon, and taking the supremum proves the diameter bound. "
                        + "The construction asserts existence and does not assert effective computability."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Application (§9.2): irrational rotation, finite external-time codes, and the sharp autonomous "
                + "obstruction. Let Phase = AddCircle(1) = ℝ/ℤ, with [t] denoting the class of t, and let o : Phase → ℂ "
                + "be AddCircle.toCircle viewed in the complex plane. For every real α define Rα(x) = x + [α] and "
                + "Rαⁿ(x) = x + n • [α], for every n ∈ ℕ including zero. The action alphabet is Unit and F((),x) = "
                + "Rα(x). Thus runWord F w x = Rα^{length(w)}(x); every natural time occurs as the length of a word. "
                + "Distances below are complex chordal distances, ‖z − z′‖. Their extended-real versions are "
                + "edist(z,z′) = ENNReal.ofReal(‖z − z′‖); all displayed suprema of edist take values in ENNReal.")),
            Paragraph(Text(
                "(1) Literal exponential observation. For every t ∈ ℝ, o([t]) = Complex.exp((2πt) · Complex.I). In "
                + "particular, ‖o(x)‖ = 1 for every phase x, and o(x+y) = o(x)o(y). These identities follow from "
                + "AddCircle.toCircle_apply_mk at period 1, Circle.coe_exp, AddCircle.toCircle_add, and "
                + "Circle.norm_coe. At phase zero the same parameter α gives o(Rαⁿ(0)) = exp(2πi nα) for every n ∈ ℕ: n "
                + "• [α] = [nα], and the two exponent expressions agree by multiplication in ℂ. This is a literal "
                + "observation identity with the same α throughout.")),
            Paragraph(Text(
                "(2) Full-future chordal metric. For every real α, every x,y ∈ Phase, and every n ∈ ℕ, o(Rαⁿ(x)) − "
                + "o(Rαⁿ(y)) = (o(x) − o(y))o(n • [α]). The last factor has norm one, so the norm of this difference "
                + "equals ‖o(x) − o(y)‖. Consequently futureDistance F o x y = sup_{w : List Unit} edist(o(runWord F w "
                + "x),o(runWord F w y)) = ENNReal.ofReal(‖o(x) − o(y)‖). This includes the empty word and the entire "
                + "unbounded future, for all real α; irrationality is unnecessary here.")),
            Paragraph(Text(
                "(3) Qualitative finite code with an external time argument. For every α ∈ ℝ and every ε > 0 there "
                + "exist a finite type C, an encoder e : Phase → C, and a decoder D : C → ℕ → ℂ such that ‖D(e(x),n) − "
                + "o(Rαⁿ(x))‖ ≤ ε for every phase x and every n ∈ ℕ. Compactness of Circle and "
                + "IsCompact.finite_cover_balls give a finite set T of unit complex centers whose open ε-balls cover "
                + "Circle. Take C to be T, choose e(x) with ‖e(x) − o(x)‖ < ε, and set D(t,n) = t · o(n • [α]), viewing "
                + "t in ℂ. Multiplication by this common unit factor preserves the error, so ‖D(e(x),n) − o(Rαⁿ(x))‖ = "
                + "‖e(x) − o(x)‖ < ε, which implies the stated weak bound. This is an existence argument by compactness "
                + "and choice; it supplies neither a grid cardinality estimate nor an executable encoding algorithm. "
                + "The decoder is supplied with n externally, and the assertion imposes no autonomous finite-state "
                + "update law on the labels.")),
            Paragraph(Text(
                "(4) Every positive-period subsequence and every complex center. If α ∈ ℝ is irrational, then for "
                + "every x ∈ Phase, every μ,p ∈ ℕ with p > 0, and every c ∈ ℂ, sup_{k ∈ ℕ} edist(o(Rα^{μ+kp}(x)),c) = "
                + "ENNReal.ofReal(1 + ‖c‖). Indeed pα is irrational by Irrational.natCast_mul. "
                + "AddCircle.denseRange_zsmul_coe_iff at period 1 gives density of its integer multiples in Phase; "
                + "denseRange_zsmul_iff_nsmul gives density of its natural multiples in this compact additive group. "
                + "Translation by x + μ • [α] and the homeomorphism AddCircle.homeomorphCircle at period 1 carry that "
                + "dense range to k ↦ o(Rα^{μ+kp}(x)) in Circle. The offset and period here are arbitrary subject only "
                + "to μ ∈ ℕ and p ∈ ℕ, p > 0.")),
            Paragraph(Text(
                "To obtain the exact supremum in (4), the triangle inequality gives ‖z − c‖ ≤ 1 + ‖c‖ for every unit "
                + "complex z. If c = 0, every such z has distance 1. If c ≠ 0, the unit point z* = −(1/‖c‖)c satisfies "
                + "‖z* − c‖ = 1 + ‖c‖. Let M be the extended supremum along the dense subsequence. The set of z in "
                + "Circle satisfying edist(z,c) ≤ M is closed by continuity and contains the dense range, hence "
                + "contains z*. It follows that ENNReal.ofReal(1 + ‖c‖) ≤ M, giving equality with the upper bound. The "
                + "supremum need not be achieved at a particular subsequence time. No restriction on the modulus of c "
                + "is imposed.")),
            Paragraph(Text(
                "(5) Obstruction for every autonomous finite machine. Fix any irrational α, any x ∈ Phase, any finite "
                + "type S, any total map G : S → S, any readout h : S → ℂ, and any initial state q ∈ S. Define "
                + "E(α,x,G,h,q) = sup_{n ∈ ℕ} edist(h(Gⁿ(q)),o(Rαⁿ(x))). The supplied q makes S nonempty. The "
                + "finite-orbit theorem finite_orbit_and_readout_eventually_periodic supplies μ,p ∈ ℕ for this very "
                + "G,h,q with 0 < p and μ+p ≤ |S|, such that for every t ≥ μ both G^{t+p}(q) = Gᵗ(q) and h(G^{t+p}(q)) "
                + "= h(Gᵗ(q)). Iterating this tail equality gives h(G^{μ+kp}(q)) = c for every k ∈ ℕ, where c = "
                + "h(G^μ(q)) is the actual readout of this machine at μ.")),
            Paragraph(Text(
                "Apply (4) using precisely that μ, p, and c, with the original α and x. The same machine therefore "
                + "satisfies E(α,x,G,h,q) ≥ sup_{k ∈ ℕ} edist(h(G^{μ+kp}(q)),o(Rα^{μ+kp}(x))) = ENNReal.ofReal(1 + "
                + "‖h(G^μ(q))‖) ≥ 1. The first inequality is restriction of the all-time supremum to those times; "
                + "symmetry of edist identifies the restricted errors with (4). Thus E ≥ 1 for every finite S, G, "
                + "arbitrary complex h, and q, for every initial phase x. This argument uses no bound or unit-circle "
                + "assumption on the machine readout. A clock or a fresh observation is not an input to G or h.")),
            Paragraph(Text(
                "(6) Sharp attainment by one state. For every real α and every x ∈ Phase, take S = Unit, G = id, "
                + "h(()) = 0, and q = (). At every natural time the error is ‖0 − o(Rαⁿ(x))‖ = 1, so E(α,x,id,0,()) = 1 "
                + "exactly. Combined with (5), this is the attained optimal all-time error over autonomous finite "
                + "machines when α is irrational. The attainment statement itself does not require irrationality.")),
            Paragraph(Text(
                "(7) No finite predictor or deterministic invariant cover below error one. For every irrational α, "
                + "every real ε with 0 ≤ ε < 1, and every natural state budget s with 1 ≤ s, both HasFinitePredictor F "
                + "o ε s and HasFiniteInvariantCover F o ε s are false. To see the first assertion, a proposed "
                + "predictor would have a nonempty finite S with |S| ≤ s, initialization e : Phase → S, transition G : "
                + "Unit → S → S, and readout h : S → ℂ, satisfying the error bound for every phase and every finite "
                + "word, including the empty word. At x = 0 and w = List.replicate n (), its state is (G ())ⁿ(e(0)). "
                + "Hence its E(α,0,G (),h,e(0)) is at most ENNReal.ofReal(ε), contradicting (5) and ε < 1. "
                + "Nonnegativity of ε is used when converting the metric bounds to ENNReal.")),
            Paragraph(Text(
                "For the cover assertion in (7), the existing finite_predictor_iff_forward_invariant_cover applies "
                + "because Phase is nonempty, ℂ is a metric space, F is total, ε ≥ 0, and s ≥ 1. A qualifying cover has "
                + "a nonempty finite index type I with |I| ≤ s, nonempty sets C(i) covering Phase, a deterministic "
                + "successor δ : Unit → I → I, and centers y : I → ℂ. It must satisfy Rα[C(i)] ⊆ C(δ((),i)) and sup_{x "
                + "∈ C(i)} edist(o(x),y(i)) ≤ ENNReal.ofReal(ε) for every i; members may overlap. Choosing an initial "
                + "containing member and following δ would produce the forbidden predictor. Conversely, the general "
                + "equivalence obtains cover members from all reachable pairs of true and machine states and removes "
                + "empty members, as described above. Its additional conclusion bounds every member's full-future "
                + "diameter by ENNReal.ofReal(2ε), even for an infinite index set. A finite cover by small static balls "
                + "alone does not supply the deterministic successor condition.")),
            Paragraph(Text(
                "The finite external-time code in (3) and the autonomous obstruction in (5) concern different access "
                + "to time. In (3), n enters the decoder directly; in (5), every time dependence must pass through "
                + "iteration of a finite state. Clauses (1), (2), (3), and (6) hold for every real α. The density, "
                + "machine obstruction, and cover exclusion in (4), (5), and (7) require irrational α. At ε = 1 the "
                + "zero-output machine attains the threshold, and the single cover member Phase with center 0 and its "
                + "own successor also has radius 1. These are statements about exact real and complex objects, with no "
                + "physical precision or resource equivalence asserted.")),
            Paragraph(Text(
                "Reused repository sources. The following source identities refer to the-omega-institute/trureturing "
                + "at revision 1382eb6d44503e5394acc2750f0f527605a4104b. The finite-period witness is from "
                + "D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean, declaration "
                + "D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic, "
                + "frozen GID D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound, statement_id "
                + "sha256:259d232d95c1ca485bdaeb0bf7eb8d9a839164d9e3964dab0743ddec9dc41953. The full-word convention is "
                + "runWord from D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean, frozen GID "
                + "D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality, statement_id "
                + "sha256:596c4a4d2f7b32214efd9faeaf871871224bcfd40c20e59cf2c9f470cb569370.")),
            Paragraph(Text(
                "The predictor, cover, and full-future definitions and their equivalence are from "
                + "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.lean, in namespace "
                + "D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover: HasFinitePredictor, IsInvariantCover, "
                + "HasFiniteInvariantCover, futureDistance, and finite_predictor_iff_forward_invariant_cover. Their "
                + "frozen GID is D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover, statement_id "
                + "sha256:8fd0f536d8a49fa25b1160aa7f128c4c14c87f832bc668212846fcadd2ece4a5. The application uses these "
                + "existing definitions with X = Phase, A = Unit, Y = ℂ, F((),x) = x + [α], and o = AddCircle.toCircle "
                + "viewed in ℂ.")),
            Paragraph(Text(
                "Pinned Mathlib sources. All Mathlib references here use revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d. Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean "
                + "supplies AddCircle.toCircle_apply_mk, AddCircle.toCircle_add, AddCircle.continuous_toCircle, "
                + "AddCircle.homeomorphCircle and AddCircle.homeomorphCircle_apply; "
                + "Mathlib/Analysis/Complex/Circle.lean supplies Circle.coe_exp, Circle.norm_coe and the compact "
                + "unit-circle setting. Mathlib/Topology/MetricSpace/Pseudo/Basic.lean supplies "
                + "finite_cover_balls_of_compact and its alias IsCompact.finite_cover_balls. "
                + "Mathlib/NumberTheory/Real/Irrational.lean supplies Irrational.natCast_mul, and "
                + "Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean supplies AddCircle.denseRange_zsmul_coe_iff. "
                + "In Mathlib/Topology/Algebra/Group/SubmonoidClosure.lean, denseRange_zsmul_iff_nsmul is the additive "
                + "form generated from denseRange_zpow_iff_pow by to_additive. These supply the compact-cover and "
                + "density steps; the remaining displayed calculations use unit norm, the triangle inequality, "
                + "continuity, closure_minimal, and restriction of a supremum.")))));
}
