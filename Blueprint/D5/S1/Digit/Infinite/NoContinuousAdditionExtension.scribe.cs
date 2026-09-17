using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class NoContinuousAdditionExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addition on Infinite Legal Digit Streams.",
        H("Addition on Infinite Legal Digit Streams"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-continuous-addition-extension-property"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/NoContinuousAdditionExtension.ExtendsFiniteAddition"),
                H("Agreement with finite addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operation sends the digit rows of any two natural numbers to the digit row of their sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("no-continuous-addition-extension-result"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/NoContinuousAdditionExtension.result"),
                H("Separate continuity obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is no binary operation on the legal infinite digit streams that is continuous "
                    + "in each variable separately and agrees with addition on all natural number digit rows."))),
                DescribeRole.Theorem))));
}
