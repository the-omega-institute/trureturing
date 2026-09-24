using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TwistedResetPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TwistedResetPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact path sums and support for complement-twisted reset loops.",
        H("Twisted Reset Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-power-support"),
                DeclarationHandle.Create(Prefix + "twisted_power_support"),
                H("Twisted power support"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite suffix carrier and real parameter, a nonzero complement-twisted return of "
                    + "length L starts at suffix less than L. If the terminal suffix were at least L, every edge "
                    + "would have to increment. Such a path preserves its sign and cannot close at the complemented "
                    + "start."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-marginal"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_marginal"),
                H("Exact complete-prefix marginal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix the start and all n subsequent states. Sum the transition product over every G-step "
                    + "continuation ending at the complemented start. The result is the prefix transition product "
                    + "times the G-th matrix-power entry between its endpoint and the complemented start. No "
                    + "initial stationary weight occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-support"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_support"),
                H("Support of every complete prefix"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonnegative parameter, the entire prefix mass vanishes whenever the starting suffix is "
                    + "at least n plus G. Each individual path weight is bounded by the corresponding matrix-power "
                    + "entry, and concatenation bounds its closing contribution by a twisted return outside the "
                    + "allowed support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-twisted-prefix-total-mass"),
                DeclarationHandle.Create(Prefix + "twisted_prefix_total_mass"),
                H("Total prefix mass"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing over the start and every full prefix gives exactly the twisted loop mass at length n "
                    + "plus G. Successively summing each transition composes the prefix with the closing matrix "
                    + "power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedresetpaths-loop-mass-pos"),
                DeclarationHandle.Create(Prefix + "loop_mass_pos"),
                H("Positive loop mass"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k at least two and a positive parameter, the twisted loop mass is positive at every "
                    + "length at least two. Odd lengths admit reset-only loops. Even lengths admit one increment "
                    + "followed by an odd number of resets. Positivity follows from actual transition weights, "
                    + "without a lower bound on a stationary mass."))),
                DescribeRole.Theorem))));
}
