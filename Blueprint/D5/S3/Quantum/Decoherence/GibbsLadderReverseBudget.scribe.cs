using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class GibbsLadderReverseBudgetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/basso2026modularfluctuation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reverse mean budget fixes the sharp logarithmic rate of forward variance.",
        H("Forward variance under a reverse mean budget"),
        Blocks(
            Theorem("variance_lower_bound", "A finite-budget variance floor",
                "Split the inverse tilted probability at a positive cutoff R. Its mass above R is "
                + "at most (B + 1/(eβ))/R under the reverse mean budget B. The forward variance "
                + "about a controls the contribution from outside a radius δ below the cutoff."),
            Theorem("variance_exponential_floor", "Strict positivity at finite budget",
                "When 0 < δ < a, an explicit choice of the reverse cutoff gives a strictly positive "
                + "lower bound on the forward centered second moment for every finite nonnegative B."),
            Theorem("exists_calibrated_gibbs_rate", "Calibrated Gibbs ladders attain the exponent",
                "The spacing tends to the prescribed positive forward mean, which it realizes "
                + "exactly for each sufficiently large ladder. Per level, the reverse mean tends "
                + "to a(1 − exp(−βa)), and the log of the forward variance tends to −βa."),
            Theorem("tendsto_log_inf_variance", "Sharp logarithmic rate",
                "At inverse temperature β > 0 and forward mean a > 0, the log of the infimum "
                + "forward variance divided by the reverse mean budget B tends to "
                + "−β/(1 − exp(−βa)) as B grows. The result holds for finite reflected-tilt laws, "
                + "for cyclic Gibbs ladders, and for every class between these two."))));

    private static DocumentBlock.Describe Theorem(string name, string heading, string statement) =>
        Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Module + name),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))),
            DescribeRole.Theorem);
}
