using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeGrowthRoundingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeGrowthRounding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original decimal growth and its integer floors provide the asymptotic arithmetic inputs used by the native small-ball interfaces.",
        H("Original growth, rounding, and native scale budgets"),
        Blocks(
            Theorem("decimal-exponent-index", "decimalExponent_index", "The decimal exponent satisfies n + 1 ≤ decimalExponent n for every natural n."),
            Theorem("scale-tends-to-infinity", "scale_tendsto", "The natural scale sequence, cast to the reals, tends to infinity along atTop."),
            Theorem("signal-exponential-bounds", "signal_exponential_bounds", "For 0 ≤ r < 1, 0 < β, nonnegative phi r, and a sufficiently large L, the floored signalSize r β L is bounded below by one quarter of exp((phi r / β − phi r)L) and above by exp((phi r / β − phi r)L + log((1+r)/(1-r)))."),
            Theorem("signal-log-rounding", "signal_log_rounding", "For positive signalSize, the logarithm of the population-times-centering exponential divided by signalSize is nonnegative, at most the reciprocal signal count, and equals log population − center − log signalSize."),
            Theorem("original-polynomial-scales", "original_polynomial_scales", "For 0 < r < 1, 0 < β < 1 and every fixed natural p, both scale n ^ p divided by signalSize r β (scale n) and by population r β (scale n) tend to zero."),
            Theorem("original-density-scales", "original_density_scales", "For 0 < r < 1 and every fixed p, scale n ^ p times the original signal density signalSize/population tends to zero."),
            Theorem("cell-logit-identity", "cell_logit_identity", "Under the stated positivity, strict population, and compensation hypotheses, cellLogit is exactly the sum of the two compensation logarithms, the final-floor logarithmic error, and the occupancy logarithm displayed by the Lean theorem."),
            Theorem("cell-logit-bound", "cell_logit_bound", "With compensation and occupancy ratio at most one half, the absolute cell logit is bounded by twice L times compensation, plus the reciprocal signal count, plus twice the occupancy ratio."),
            Theorem("compensation-density-bound", "compensation_density_bound", "For q < M, 0 ≤ r, and q/M ≤ 1/2, compensation M q r is at most 2 r (q/M)."),
            Theorem("original-populations-tend-to-infinity", "original_populations_tendsto", "For 0 < r < 1 and 0 < β < 1, both integer populations signalSize r β (scale n) and population r β (scale n) tend to infinity."),
            Theorem("original-compensation-scales", "original_compensation_scales", "For 0 < r < 1 and every fixed p, scale n ^ p times the original compensation tends to zero."),
            Theorem("original-cell-logit-precision", "original_cell_logit_precision", "For 0 < r < 1 and 0 < β < 1, scale n times the absolute original cell logit tends to zero."),
            Theorem("original-cell-logit-bounds", "original_cell_logit_bounds", "For positive κ₀ and the stated r, β hypotheses, eventually the cell logit has absolute value at most κ₀/(2 scale n), and its negative lies between log(7/8) and log(9/8)."),
            Theorem("original-tail-rates", "original_tail_rates", "For 0 < r < 1 and β > 1/2, both fixed Chernoff gaps (8 log 4 − 6) − phi r/β and (8 log 4 − 6) − 2 phi r are positive."),
            Theorem("original-tail-scales", "original_tail_scales", "For 0 < r < 1 and β > 1/2, the two original all-row tail payments specified by the Lean expression tend to zero along scale n."),
            Theorem("original-native-scale-conditions", "original_native_scale_conditions", "Given positive constants and M₀, the original populations and scales eventually satisfy the finite native relative, occupancy, and variance interface inequalities for every M ≥ M₀."),
            Theorem("original-central-score-condition", "original_central_score_condition", "For 0 < r < 1, the original central counts eventually satisfy the finite reference-variance score condition."),
            Definition("root-failure-budget", "rootFailureBudget", "The explicit full-root failure budget is the sum of the root precision, variance, and finite-scale payments used by the native laws."),
            Theorem("original-root-failure-budget-zero", "original_root_failure_budget_zero", "For 0 < r < 1, every fixed choice of root parameters gives a rootFailureBudget tending to zero along the original scale sequence."),
            Theorem("original-rectangle-scale-budget", "original_rectangle_scale_budget", "For 0 < r < 1 and positive β, the native rectangle cardinality and feedback payments admit constants cN and CN and a budget tending to zero, uniformly over supports and experiments."),
            Theorem("original-complete-root-budget", "original_complete_root_budget", "For 0 < r < 1 and β > 1/2, complete calibrated roots have arbitrarily fine A-logit precision and a vanishing uniform root budget on the original scales."),
            Theorem("original-rectangle-feedback-scales", "original_rectangle_feedback_scales", "For 0 < r < 1, positive c and C, and positive η and T, the rectangle feedback scale has a vanishing slope and the stated uniform cardinality bounds eventually hold."),
            Theorem("original-full-environment-small-ball", "original_full_env_small_ball", "Under the original hypotheses and the decimal-alpha identity, there are positive constants and a vanishing budget such that every nonzero integer root origin has the complete native environment small-ball bound."),
            Provenance())));

    private static Describe Theorem(string id, string name, string statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement + " The exact quantifiers, hypotheses, constants, and conclusion are the compiled Lean statement.")),
                Paragraph(Text("The proof is repo-derived and uses the native arithmetic, calibration, and small-ball interfaces. Classical references consulted for the surrounding estimates include Erdos–Littlewood–Offord, Le Cam's Poisson-binomial comparison, Chernoff moderate deviations, and saddlepoint bounds; those works supply context and tools, while this theorem's stated result is repo-derived."))),
            DescribeRole.Theorem);

    private static Describe Definition(string id, string name, string statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement + " The definition is reproduced by the compiled Lean source."))),
            DescribeRole.Definition);

    private static ScribeNode Provenance() =>
        Paragraph(Text("Literature notes in Library/Estimation cover discrete Gaussian rounding, logarithmic forms, rare-event and moderate-deviation estimates, Poisson-binomial approximation, hypergeometric tails, and saddlepoint methods. They are cited as classical tools; all displayed declarations remain repo-derived."));
}
