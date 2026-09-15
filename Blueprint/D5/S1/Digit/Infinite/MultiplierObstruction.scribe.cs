using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class MultiplierObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplication on Infinite Legal Digit Streams.",
        H("Multiplication on Infinite Legal Digit Streams"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multiplierobstruction-multiplier-obstruction"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/MultiplierObstruction.multiplier_obstruction"),
                H("The multiplier obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural number m at least two, no continuous self-map of the legal "
                    + "streams sends the digit row of n to the digit row of m times n for every "
                    + "natural number n."))),
                DescribeRole.Theorem))));
}
