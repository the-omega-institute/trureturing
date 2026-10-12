using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class PowerMajorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power sums and finite Holder.", H("PowerMajorization"), Blocks(
            Paragraph(Text("Weak log-majorization of nonnegative decreasing sequences implies domination of every positive power sum. Finite scalar Holder bounds the product of singular-value powers with positive exponents satisfying the reciprocal identity.")),
            Paragraph(Text("The source is Alex Meiburg's Apache-2.0 Physlib at revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the "
                + "Schatten product Holder inequality. No mathematical originality is claimed.")))));
}
