using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenChronology;

internal sealed class GoldenFactorParikhMagnusBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality of the fixed represented Chen signatures is equivalent to equality of the legal golden factors.",
        H("Golden Factor Matrix Recovery"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("golden-factor-parikh-magnus-bridge-source"),
                DeclarationHandle.Create("D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge.golden_factor_eq_iff_step_two_signature_eq"),
                H("Source-linked mathematical interpretation"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Equality of the fixed represented Chen signatures is equivalent to equality of the legal golden factors.")),
                    Paragraph(Text("The two first-degree entries recover length. A single central second-order coordinate then recovers the legal word. Prime labels and absolute occurrence indices are outside this claim.")),
                    Paragraph(Text("This mirror supplies commentary only. The named Lean declaration and its kernel report own the exact statement and verification status.")))))));
}
