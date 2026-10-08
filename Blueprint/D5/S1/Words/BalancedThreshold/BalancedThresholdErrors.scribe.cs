using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdErrorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic family has an exact complete-quotient ratio for every continuant error.",
        H("The infinite error orbit"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-uniform-continuant-errors"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdErrors.uniform_continuant_errors"),
            H("Positive alternating tails propagate nonzero errors and their exact ratio"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every parameter at least five and every computed continuant index, "
                + "the predecessor discrepancy is the negative complete quotient times "
                + "the current discrepancy. The initial fractional tail is exceptional; "
                + "later tails alternate between the quadratic root and its reciprocal "
                + "partner. Their reciprocal identities propagate the discrepancy ratio "
                + "through the actual continuant recurrence by unbounded induction. "
                + "Strict tail positivity preserves nonvanishing at every step. "
                + "The result supplies the coefficient for the derived return strip; "
                + "it does not establish the coloured return bound or critical exponent."))),
            DescribeRole.Theorem))));
}
