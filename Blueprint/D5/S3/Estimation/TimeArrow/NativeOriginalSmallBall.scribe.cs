using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeOriginalSmallBallDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeOriginalSmallBall.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original decimal sequence supplies the native cube and environment small-ball conclusions through the frozen parity and calibration interfaces.",
        H("Original decimal sequence and native small-ball conclusions"),
        Blocks(
            Definition("decimal-numerator", "decimalNumerator", "decimalNumerator n is the finite base-ten numerator formed from all decimal exponents through index n."),
            Definition("decimal-alpha", "decimalAlpha", "decimalAlpha is the convergent real series whose j-th term is the reciprocal of denominator j."),
            Definition("decimal-tail", "decimalTail", "decimalTail n is the positive tail of the same reciprocal-denominator series after index n."),
            Theorem("original-native-environment-small-ball", "original_native_environment_small_ball", "For 0 < r < 1, β > 1/2, β < 1, and the decimal-alpha identity, there exist positive native constants cN, CN, and c such that every nonzero integer root origin admits a positive cell constant and a budget tending to zero; eventually the conditional native environment failure mass is bounded by that budget for every support and experiment."),
            Theorem("original-cube-environment-small-ball", "original_cube_environment_small_ball", "Under the same original hypotheses, the cube observation equivalence and original cube probability satisfy the complete-window small-ball conclusion with a vanishing failure budget, uniformly over dimensions, supports, experiments, and nonzero integer root origins."),
            Provenance())));

    private static Describe Theorem(string id, string name, string statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement + " The complete quantifier order and all native readout expressions are the compiled Lean statement.")),
                Paragraph(Text("The result is repo-derived from the native growth, parity-kernel, rectangle, calibration, and finite-support interfaces. Literature notes on Littlewood–Offord small-ball bounds, hypergeometric concentration, Poisson approximation, and rare-event estimates describe related tools but do not replace this formal statement."))),
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
        Paragraph(Text("Library/Estimation notes consulted include discrete Gaussian rounding, logarithmic-form estimates, Littlewood–Offord small-ball theory, hypergeometric concentration, Poisson-binomial approximation, and saddlepoint methods. These are contextual references; the declarations above are repo-derived."));
}
