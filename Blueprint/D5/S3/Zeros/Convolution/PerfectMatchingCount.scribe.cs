using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class PerfectMatchingCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/PerfectMatchingCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count fixed-point-free involutions using the pinned Mathlib cycle-type formula.",
        H("Perfect Matching Count"),
        Blocks(
            Paragraph(Text(
                "The proof specializes Equiv.Perm.card_of_cycleType_mul_eq to h cycles "
                + "of length two. It supplies the cross-edge factor for the proposed "
                + "MatchingMonomialFiber equivalence.")),
            Describe.Lean(
                DescribeId.Create("involution-count-product"),
                DeclarationHandle.Create(Prefix + "card_fixedPointFreeInvolution_mul"),
                H("Exact Product Count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite type of cardinality 2h, its number of fixed-point-free "
                    + "involutions times h! times 2^h equals (2h)!."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involution-count-quotient"),
                DeclarationHandle.Create(Prefix + "card_fixedPointFreeInvolution"),
                H("Factorial Quotient Count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positivity of the denominator turns the product equality into the "
                    + "exact natural-number factorial quotient, including h = 0."))),
                DescribeRole.Theorem))));
}
