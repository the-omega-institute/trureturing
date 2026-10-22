using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayWeightCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact full Golay weight enumerator.", H("All 4096 codewords"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-counts"),
                DeclarationHandle.Create(Prefix + "finite_row_counts"),
                H("Complete row certificates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the sixty-four prefix rows contains sixty-four distinct messages. Their actual packed weights are counted by kernel reduction. The separately proved decoding identity ties the packed computation to the polynomial linear code."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weight-choices"),
                DeclarationHandle.Create(Prefix + "finite_weight_choices"),
                H("No other weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every message pair has weight zero, eight, twelve, sixteen or twenty-four; there is no sampling or truncation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weight-enumerator"),
                DeclarationHandle.Create(Prefix + "exact_weight_enumerator"),
                H("1 + 759 z^8 + 2576 z^12 + 759 z^16 + z^24"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite counts are transported through the actual weight identity and summed, giving coefficients one, seven hundred fifty-nine, two thousand five hundred seventy-six, seven hundred fifty-nine and one. Faithful enumeration identifies these with all actual codewords. This is the classical Golay enumerator, not a novelty claim, a moonshine character or a Monster representation."))), DescribeRole.Theorem))));
}
