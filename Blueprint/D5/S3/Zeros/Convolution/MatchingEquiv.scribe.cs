using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class MatchingEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/MatchingEquiv.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decompose each matching monomial fiber and count its two factors.",
        H("Matching Fiber Equivalence"),
        Blocks(
            Paragraph(Text(
                "Square vertices choose distinct partners outside the monomial support. "
                + "Linear vertices form the pairs of a fixed-point-free involution. "
                + "Rebuilding the edges and their local choices proves the inverse construction.")),
            Describe.Lean(
                DescribeId.Create("fiber-cardinality"),
                DeclarationHandle.Create(Prefix + "card_matchingMonomialFiber"),
                H("Exact Fiber Cardinality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The embedding count multiplies the exact factorial quotient counting "
                    + "cross-edge involutions, for arbitrary n, k, S and T."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fiber-cardinality-product"),
                DeclarationHandle.Create(Prefix + "card_matchingMonomialFiber_mul"),
                H("Division-free Count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product equality supplies the same count without natural-number "
                    + "division, for use in coefficient fields."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-fiber-coefficient"),
                DeclarationHandle.Create(Prefix + "coeff_matchingSum_fiber"),
                H("Matching Coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Formula (C) follows by casting the product count into Q. The powers "
                    + "of two cancel and leave only the alternating sign and factorial ratios."))),
                DescribeRole.Theorem))));
}
