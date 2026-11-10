using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233128FibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal single-row certificate for the seven-column square strip.",
        H("Consumed kernel certificate"),
        Blocks(Paragraph(Text(
            "This module contains private proof helpers. Exact scanner fibres turn "
            + "the individual-colour sum into a sum over one label row. The single-row "
            + "identities are consumed by the public finite_certificate and result in "
            + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip. "
            + "No new public declaration is introduced here.")))));
}
