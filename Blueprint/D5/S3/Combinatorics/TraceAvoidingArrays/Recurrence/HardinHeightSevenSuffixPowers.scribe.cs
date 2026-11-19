using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinHeightSevenSuffixPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Later powers of the height-seven column quotient",
        H("Powers from 25 through 48"),
        Blocks(Paragraph(Text(
            "The first step multiplies the checked vector at exponent 24 by the same quotient matrix. "
            + "Every subsequent step through exponent 48 is checked componentwise. Appending these vectors "
            + "to the initial table gives the powers used by the full-state height-seven certificate.")))));
}
