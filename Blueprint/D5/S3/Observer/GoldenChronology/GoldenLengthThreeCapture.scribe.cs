using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class GoldenLengthThreeCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete length-three factor object has four states and twelve ordered distinct pairs.",
        H("Shared-Arena Golden Capture"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("golden-length-three-capture-source"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenChronology/GoldenLengthThreeCapture.full_presentation_faithful_but_not_irredundant"),
                H("Source-linked mathematical interpretation"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complete length-three factor object has four states and twelve ordered distinct pairs.")),
                    Paragraph(Text("The two-coordinate analysis view has unique capture counts two and six. Adding the full matrix peer makes all three exclusive captures zero. These are explicitly analysis views, not a designated-root maximal-catalog admission certificate.")),
                    Paragraph(Text("This mirror supplies commentary only. The named Lean declaration and its kernel report own the exact statement and verification status.")))))));
}
