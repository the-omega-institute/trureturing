using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinHeightSevenPrefixPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initial powers of the height-seven column quotient",
        H("Successor multiplicities and powers through 24"),
        Blocks(Paragraph(Text(
            "Each of the 50 classes has a multiset of successor classes. The multiplicity of a class "
            + "is the entry of the quotient matrix. Its action sums the entries of a vector over that "
            + "multiset. The table starts with one on each class and the kernel verifies all 24 "
            + "successive multiplications through exponent 24.")))));
}
