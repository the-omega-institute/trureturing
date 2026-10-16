using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class BinaryShiftExactBitLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At error in [0,1), binary shift prediction through time H requires exactly H plus one bits.",
        H("Exact State and Bit Counts for the Binary Shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-predictor"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.HasFiniteHorizonPredictor"),
                H("Prediction through a prescribed horizon"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a deterministic controlled system F with observation o in a metric space, "
                    + "a predictor with state budget s consists of a nonempty finite state set S "
                    + "of cardinality at most s, an initialization e, total deterministic transitions G, "
                    + "and a readout h. For every initial state x and every action word w of length "
                    + "at most H, the distance between the predicted and true outputs is at most "
                    + "epsilon. The empty word is included. Transitions receive only the current "
                    + "state and action; readout receives only the state. Neither receives the time "
                    + "or a new observation. The predictor may depend on H and epsilon."))),
                DescribeRole.Definition),
            new DocumentBlock.Section(H("An autonomous rational clock on the circle"), Blocks(
            Paragraph(Text(
                "Fix any real rotation increment α, any integer p, any natural q > 0, and any natural horizon H. "
                + "Let X = ℝ/ℤ, represented in Lean by UnitAddCircle, and let rep(x) be the unique representative t "
                + "in [0,1). The true transition is F((),x) = x + α modulo one, with the singleton action alphabet "
                + "Unit. Observe the complex phase o(x) = exp(2πit). This is independent of the chosen real lift of "
                + "x because the exponential has period one in t.")),
            Paragraph(Text(
                "Use the nonempty state set S = ℤ/qℤ, represented by ZMod q; it has exactly q elements "
                + "(ZMod.card). Initialize once by e_q(x) = round(q rep(x)) modulo q. The total autonomous "
                + "transition is G((),j) = j + p modulo q, and the readout is h(j) = exp(2πik/q), where k is any "
                + "integer representing j. Changing k by a multiple of q leaves the readout unchanged; this is the "
                + "standard character ZMod.stdAddChar, with its integer formula ZMod.stdAddChar_coe.")),
            Paragraph(Text(
                "For every initial circle point x and every natural n, repeated addition gives G^n(e_q(x)) = "
                + "e_q(x) + np modulo q. The true state is F^n(x) = x + nα modulo one, with output exp(2πi(t + "
                + "nα)). The additive iteration identity is add_right_iterate_apply. These formulas hold for all n, "
                + "including zero; only the uniform error estimate below restricts n to the horizon.")),
            Paragraph(Text(
                "Write t = rep(x), r = round(qt), and u = r/q as real numbers. The nearest-integer bound "
                + "abs_sub_round gives |r - qt| ≤ 1/2, hence |u - t| ≤ 1/(2q), since q is positive. The "
                + "representative identity AddCircle.coe_equivIco and the quotient formula ZMod.toAddCircle_intCast "
                + "identify the encoded circle point with u modulo one and x with t modulo one. Projection to the "
                + "quotient does not increase the norm (QuotientAddGroup.norm_mk_le_norm), so the initial circle "
                + "error is ‖ZMod.toAddCircle(e_q(x)) - x‖ ≤ 1/(2q). This also covers rounding across the seam at "
                + "zero.")),
            Paragraph(Text(
                "At time n choose the real lifts a_n = u + np/q for the predicted phase and b_n = t + nα for the "
                + "actual phase. Their difference is (u - t) + n(p/q - α). The triangle inequality therefore gives "
                + "|a_n - b_n| ≤ 1/(2q) + n|α - p/q|. For any real a,b, factoring out the unit complex number "
                + "exp(2πib) and applying Real.norm_exp_I_mul_ofReal_sub_one_le at 2π(a-b) gives |exp(2πia) - "
                + "exp(2πib)| ≤ 2π|a-b|. Combining the two estimates, for every x and every natural n ≤ H the "
                + "complex output distance is at most π/q + 2πn|α - p/q| ≤ π/q + 2πH|α - p/q|.")),
            Paragraph(Text(
                "In HasFiniteHorizonPredictor the parameters are X = UnitAddCircle, A = Unit, Y = ℂ with its "
                + "usual metric, F and o as above, horizon H, error ε = π/q + 2πH|α - p/q|, and state budget s = q. "
                + "The witness is S = ZMod q with initialization e_q, transition G and readout h. For a word w of "
                + "length n, the recursive definition ControlledBehaviorUniversality.runWord applies exactly n "
                + "copies of the single action. Induction on w gives runWord G w (e_q(x)) = e_q(x) + np and runWord "
                + "F w x = x + nα in their respective quotients. Thus the displayed bound is precisely the required "
                + "distance inequality for every w with length at most H. The empty word reads the initialized "
                + "state. After initialization, neither transition nor readout receives time or a new observation; "
                + "the same fixed clock works at every read time.")),
            Paragraph(Text(
                "The cases H = 0 and q = 1 require no exception. At horizon zero the bound is π/q and includes "
                + "the initial readout. At q = 1 the clock has one state, its transition is constant and its "
                + "readout is 1; the same estimate applies. If α = p/q, the drift term vanishes and the error bound "
                + "π/q holds for every natural time with this same clock.")),
            Paragraph(Text(
                "The number q is the cardinality of this explicit construction and therefore an achievable state "
                + "budget; no minimum-state or optimality assertion follows. This application gives no exact bit "
                + "law, precision-complexity bound, computability guarantee or initialization, storage or "
                + "running-cost bound. Initialization remains an arbitrary map of the real initial phase in the "
                + "observational model; no physical implementation with finite precision is asserted. The "
                + "binary-shift theorem below concerns a different system with real sign outputs and retains its "
                + "exact minimum 2^(H+1) for 0 ≤ ε < 1. The clock estimate is an application of the stated "
                + "rounding, quotient, iteration and chord bounds, with no claim of research novelty.")))),
            Describe.Lean(
                DescribeId.Create("binary-observation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binaryObservation"),
                H("The leading bit as a sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An actual state is an infinite binary sequence indexed by the natural numbers. "
                    + "False represents zero and true represents one. The observation is minus one "
                    + "raised to the leading bit: zero gives one, and one gives minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-binary-shift-bit-law"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binary_shift_exact_bit_law"),
                H("The exact minimum state and bit counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be the left shift, so that coordinate j after one step is the old "
                        + "coordinate j plus one. For every natural horizon H and every real error "
                        + "epsilon with zero less than or equal to epsilon and epsilon less than one, "
                        + "the least achievable autonomous state budget is 2^(H+1). Its ceiling "
                        + "base-two logarithm, expressed by Nat.clog, is H+1. The action alphabet "
                        + "is a singleton, so the transitions are autonomous. Predictor outputs "
                        + "may be arbitrary real numbers. Both H equal to zero and epsilon equal "
                        + "to zero are included.")),
                    Paragraph(Text(
                        "For the upper bound, store the first H+1 bits. Read the sign of the first "
                        + "bit, shift left at each step, and append zero. Induction on the number "
                        + "of steps shows that each remaining coordinate equals the corresponding "
                        + "original coordinate. Thus every readout through time H is exact, using "
                        + "2^(H+1) states and no additional clock.")),
                    Paragraph(Text(
                        "For the lower bound, extend every prefix of length H+1 by zeros. If two "
                        + "different prefixes had the same initialized state, their predicted "
                        + "outputs would coincide at a coordinate where their true signs differ. "
                        + "The true outputs there have distance two, while the triangle inequality "
                        + "bounds that distance by twice epsilon, which is strictly less than two. "
                        + "Initialization is therefore injective on all prefixes. Counting them "
                        + "gives the lower bound, and the ceiling logarithm of a power of two "
                        + "gives the exact bit count."))),
                DescribeRole.Theorem))));
}
