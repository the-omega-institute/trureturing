using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class LegalDigitCoveringNumberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum Covers of the Legal Digit Space.",
        H("Minimum Covers of the Legal Digit Space"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("legaldigitcoveringnumber-least-covering-number"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/LegalDigitCoveringNumber.least_covering_number"),
                H("Fibonacci minimum covering number"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real radius parameter strictly between zero and one, the least number "
                    + "of closed balls of radius theta to the L covering legal infinite Boolean digits "
                    + "is the Fibonacci count of admissible length L prefixes. The proof realizes every "
                    + "admissible prefix by zero extension and shows that every ball is contained in one "
                    + "prefix cylinder."))),
                DescribeRole.Theorem))));
}
