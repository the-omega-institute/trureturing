using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class MatchingFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/MatchingFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary symmetric fibers and a partial matching-coefficient reduction at arbitrary degree.",
        H("Matching Monomial Fibers"),
        Blocks(
            Paragraph(Text(
                "MatchingIdentity is an unproved proposition. The module proves the elementary "
                + "symmetric product fiber formula and reduces matching coefficients to a signed "
                + "fiber cardinality. It also constructs the injection assigning unused partners "
                + "to squared vertices. The perfect-matching correspondence, complete fiber count, "
                + "and all-degree matching identity are not proved.")),
            Describe.Lean(
                DescribeId.Create("symmetrization-coefficient"),
                DeclarationHandle.Create(Prefix + "symmetrize_coefficient"),
                H("Symmetrization Coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 2k <= n, the coefficient of degree n-2k is expressed through the "
                    + "frozen additive-convolution definitions and descending factorials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("elementary-product-fiber"),
                DeclarationHandle.Create(Prefix + "coeff_esymm_mul_fiber"),
                H("Elementary Product Fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For disjoint S and T, the exponent-two/exponent-one coefficient of e_i e_j "
                    + "is choose(|T|,i-|S|) when both lower bounds and total degree agree, "
                    + "and is zero otherwise. The proof constructs inverse subset-pair maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-coefficient-fiber"),
                DeclarationHandle.Create(Prefix + "coeff_matchingSum_eq_card_fiber"),
                H("Matching Coefficient Reduction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prescribed matching coefficient equals (-2)^(k-|S|) times the "
                    + "cardinality of its decorated-matching fiber. A square-choice bijection "
                    + "proves the weight is constant. The remaining cardinality is not evaluated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partner-assignments"),
                DeclarationHandle.Create(Prefix + "card_partner_embeddings"),
                H("Ordered Partner Assignments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib counts embeddings from S to the complement of S union T by "
                    + "the corresponding descending factorial. This is one factor in the "
                    + "proposed matching-fiber count, not a proof of the full count."))),
                DescribeRole.Theorem))));
}
