using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeOriginalSmallBallDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeOriginalSmallBall.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original decimal sequence supplies the native cube and environment small-ball conclusions through the parity and calibration interfaces.",
        H("Original decimal sequence and native small-ball conclusions"),
        Blocks(
            Definition("cube-parity-equivalence", "cubeParityEquiv", "cubeParityEquiv identifies a (d+1)-coordinate signed cube with the native vertex space of size 2^d while retaining the product-sign parity.", "OriginalScoreWindow"),
            Definition("cube-observation-equivalence", "cubeObservationEquiv", "cubeObservationEquiv transports every sitewise signed-cube observation to the native observation type for the chosen experiment.", "OriginalScoreWindow"),
            Definition("original-cube-probability", "originalCubeProbability", "originalCubeProbability is the original uniform-start pair or path mass obtained from the frozen parity transition kernel on signed cube observations.", "OriginalScoreWindow"),
            Theorem("original-cube-probability-eq-native", "original_cube_probability_eq_native", "For every dimension, support, experiment, and signed-cube observation, originalCubeProbability equals the native probability of its transported observation.", "OriginalScoreWindow"),
            Theorem("original-cube-conditional-mass-eq", "original_cube_conditional_mass_eq", "For every rectangle readout and predicate, the signed-cube conditional numerator and denominator sums agree with the corresponding native observation sums after cubeObservationEquiv.", "OriginalScoreWindow"),
            Definition("original-cube-score", "originalCubeScore", "originalCubeScore is the original score obtained by applying the native score to the cube observation equivalence.", "OriginalScoreWindow"),
            Definition("original-cube-inclusion", "originalCubeInclusion", "originalCubeInclusion is the posterior inclusion probability transported through the native cube observation equivalence.", "OriginalScoreWindow"),
            Definition("original-cube-group-posterior-mean", "originalCubeGroupPosteriorMean", "originalCubeGroupPosteriorMean is the sum of posterior inclusion probabilities over the complete score window selected from the transported cube history.", "OriginalScoreWindow"),
            Theorem("original-cube-group-eq-native", "original_cube_group_eq_native", "For every cube dimension, sample size, experiment, and group parameters, originalCubeGroupPosteriorMean equals the native group posterior mean after transport.", "OriginalScoreWindow"),
            Definition("decimal-numerator", "decimalNumerator", "decimalNumerator n is the finite base-ten numerator formed from all decimal exponents through index n."),
            Definition("decimal-alpha", "decimalAlpha", "decimalAlpha is the convergent real series whose j-th term is the reciprocal of denominator j."),
            Definition("decimal-tail", "decimalTail", "decimalTail n is the positive tail of the same reciprocal-denominator series after index n."),
            Theorem("original-native-environment-small-ball", "original_native_environment_small_ball", "For 0 < r < 1, β > 1/2, β < 1, and the decimal-alpha identity, there exist positive native constants cN, CN, and c such that every nonzero integer Fourier coefficient admits a positive cell constant and a budget tending to zero; eventually the conditional native environment failure mass is bounded by that budget for every support and experiment."),
            Theorem("original-cube-environment-small-ball", "original_cube_environment_small_ball", "Under the same original hypotheses, the cube observation equivalence and original cube probability satisfy the complete-window small-ball conclusion with a vanishing failure budget, uniformly over supports and experiments at the dimension d = floor(phi r * scale n / (β log 2)), for each fixed nonzero integer Fourier coefficient."),
            Provenance())));

    private static DocumentBlock.Describe Theorem(string id, string name, string statement, string scope = "NativeOriginalSmallBall") =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + scope + "." + name),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement + " The complete quantifier order and all native readout expressions are the compiled Lean statement.")),
                Paragraph(Text("The result is repo-derived from the native growth, parity-kernel, rectangle, calibration, and finite-support interfaces. Literature notes on Littlewood–Offord small-ball bounds, hypergeometric concentration, Poisson approximation, and rare-event estimates describe related tools but do not replace this formal statement."))),
            DescribeRole.Theorem);

    private static DocumentBlock.Describe Definition(string id, string name, string statement, string scope = "NativeOriginalSmallBall") =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + scope + "." + name),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement + " The definition is reproduced by the compiled Lean source."))),
            DescribeRole.Definition);

    private static DocumentBlock Provenance() =>
        Paragraph(Text("Library/Estimation notes consulted include discrete Gaussian rounding, logarithmic-form estimates, Littlewood–Offord small-ball theory, hypergeometric concentration, Poisson-binomial approximation, and saddlepoint methods. These are contextual references; the declarations above are repo-derived."));
}
