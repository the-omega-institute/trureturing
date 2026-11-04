using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded residual windows", H("Natural selectors and actual bits"),
        Blocks(Paragraph(Text("The singleton-W proof uses the exhaustive quotient split z=y, z=2y, or z>=4y and proves both W windows even with early fresh."))), []));
}
