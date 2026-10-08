using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdDisplacementsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mechanical bispecial occurrence displacements decompose into return multiplicities.",
        H("Unbounded occurrence displacements"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-return-displacements"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdDisplacements.mechanical_return_displacements"),
            H("Return multiplicities and physical discrepancy"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For each bispecial factor at any irrational frequency in (0,1), "
                + "two nonempty unimodular return candidates describe the letter "
                + "counts between any two occurrences. Strong induction on their "
                + "distance splits at the least next occurrence and constructs "
                + "nonnegative multiplicities with positive sum. Their combined "
                + "mechanical discrepancy is strictly below one. This is a physical "
                + "count estimate, without a bound on the number of intervening "
                + "occurrences. It does not establish the sharper derived-word strip, "
                + "continued-fraction indexing or realization of both candidates."))),
            DescribeRole.Theorem))));
}
