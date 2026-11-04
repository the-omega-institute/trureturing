using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldInnerNativeInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inner native unit", H("The inner native unit"), Blocks(
            Describe.Lean(DescribeId.Create("inner-unit-series"),
                DeclarationHandle.Create(Prefix + "innerUnitSeries"),
                H("A native series with constant coefficient one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In cumulative coefficient coordinates for b,z,x, the exact unit is (1-T-ST)^k (1-T)^k (1+S)^H. It has constant coefficient one over every commutative complex algebra, including the zero algebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("raw-inner-coefficient"),
                DeclarationHandle.Create(Prefix + "rawInnerCoefficient"),
                H("Signed native inverse coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generally infinite native numerator is reordered and placed in the cumulative coefficient chart. The coefficient of the inverse unit times this chart is read at the signed index (b+k,b+z+k+a1+a2,x+b+z+a0+3k+a1+a2), with zero extension outside the nonnegative chart."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("raw-inner-action"),
                DeclarationHandle.Create(Prefix + "raw_inner_action"),
                H("Exact action of the original polynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite signed monomial translations, sums, products and powers prove that multiplication by the literal original polynomial recovers the original numerator at every signed target. The native unit equation cancels only a native series unit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("raw-inner-support"),
                DeclarationHandle.Create(Prefix + "raw_inner_support"),
                H("Support of the inverse expression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse expression vanishes below b=-k. At each fixed b it vanishes below z=-(b+k+a1+a2), with the signed zero cases included. This proves support of the constructed inverse; it does not impose support on actual fields."))), DescribeRole.Theorem))));
}
