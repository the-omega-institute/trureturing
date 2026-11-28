using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Core;

internal sealed class MaximalMinorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full column minors over valuation domains",
        H("Full column minors over valuation domains"),
        Blocks(Describe.Lean(
            DescribeId.Create("valuation-domain-full-column-minor-divides-product-determinants"),
            DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Core/MaximalMinors.exists_maximal_minor_dvd_det_mul"),
            H("A single minor divides the determinants of all right products"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let A be a rectangular matrix over a valuation domain with a nonzero full column minor. "
                + "There is a fixed injective column selection whose determinant is nonzero and divides "
                + "the determinant of A times every compatible right multiplier. Total divisibility selects "
                + "a minor dividing all full minors. Expand the determinant in the rows of the transposed product. "
                + "Each selection with repeated columns has determinant zero, while each injective selection "
                + "contributes a multiple of the fixed minor."))),
            DescribeRole.Theorem))));
}
