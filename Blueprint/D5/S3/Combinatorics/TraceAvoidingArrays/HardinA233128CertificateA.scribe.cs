using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233128CertificateADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal single-row certificate for the seven-column square strip.",
        H("Single-row transfer identities"),
        Blocks(Paragraph(Text(
            "Exact scanner fibres turn the individual-colour sum into a sum over "
            + "proper label rows. A proper seven-cell label row is determined by its "
            + "first label and six choices between the two remaining labels. Thus "
            + "there are 3 times 2^6 = 192 rows to check. Their weighted vertical "
            + "compatibility sums depend only on the completed boundary class, or "
            + "on the sector before colour 2. These one-row identities yield the "
            + "finite_certificate theorem of "
            + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip.")))));
}
