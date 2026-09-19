using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class GeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass of the canonical partition.",
        H("Mass of the canonical partition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometry-sum-canonicalcelllength-eq-hull"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_eq_hull"),
                H("Total cell length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural radius, rational shift and natural depth, summing canonical cell lengths over the actual sourceCells list telescopes to the support hull length. The proof uses the actual first and last source endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometry-sum-canonicalcelllength-sq-le"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Geometry.sum_canonicalCellLength_sq_le"),
                H("Quadratic cell mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive natural radius, the sum of squared cell lengths is at most the maximum dyadic gap times the support hull length. Nonnegative cell lengths allow multiplication of the individual gap bound before summation."))),
                DescribeRole.Theorem)),
        []));
}
