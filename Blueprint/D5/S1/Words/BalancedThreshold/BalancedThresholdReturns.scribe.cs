using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdReturnsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mechanical bispecial return blocks have unimodular Parikh vectors.",
        H("Unimodular return classification"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-bispecial-returns"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdReturns.mechanical_bispecial_returns"),
            H("Two candidates with an exact factor-count identity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every irrational frequency strictly between zero and one, "
                + "each bispecial factor of the characteristic mechanical word "
                + "has two nonempty candidate return blocks. Every actual adjacent "
                + "return is one of these candidates. Their Parikh determinant has "
                + "absolute value one, and their combined count of each letter is "
                + "one more than its count in the factor. Strong induction on factor "
                + "length descends through majority blocks and reconstructs physical "
                + "returns. Complementation handles frequencies above one half. "
                + "The empty factor is included. Realization of both candidates and "
                + "their continued-fraction indexing are separate conclusions."))),
            DescribeRole.Theorem))));
}
