using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class StrictDivisorChainCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict Divisor Chains.",
        H("Strict Divisor Chains"),
        Blocks(Paragraph(Text(
            "A strict divisor chain starts at one, ends at a prescribed natural number, "
            + "and increases at every divisibility step. Weak chains allow repeated endpoints. "
            + "All endpoints are bounded by the final endpoint, so both chain types are finite. "
            + "The prime-exponent counting function is the product of the binomial composition "
            + "counts at positive lengths and is zero at length zero.")))));
}
