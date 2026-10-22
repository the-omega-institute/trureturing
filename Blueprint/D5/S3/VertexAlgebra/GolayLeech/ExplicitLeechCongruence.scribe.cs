using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitLeechCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Golay-congruence lattice mathematics.",
        H("Exact integral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"),
                DeclarationHandle.Create(Prefix + "member_iff_congruences"), H("Exact corrected congruences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterization x=m+2y, with m equal to zero or one, is equivalent to common coordinate parity, corrected Golay membership and sum(x)=4m modulo eight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-1"),
                DeclarationHandle.Create(Prefix + "member_add"), H("Actual addition closure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Odd plus odd adds the all-ones carry word. The sum condition is preserved with its exact integer carry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"),
                DeclarationHandle.Create(Prefix + "member_even_squareSum"), H("Even integral norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of integer coordinate squares is divisible by sixteen for every actual member. The normalization is the Euclidean dot product divided by eight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-3"),
                DeclarationHandle.Create(Prefix + "member_integral_pairing"), H("Integral polarization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual addition closure and the three divisible square sums imply divisibility of every coordinate dot product by eight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-4"),
                DeclarationHandle.Create(Prefix + "member_minimum_squareSum"), H("Arbitrary-vector rootlessness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Odd vectors have twenty-four nonzero coordinates; divisibility by sixteen raises the bound to thirty-two. A nonzero corrected codeword has at least eight odd half-coordinates. With zero corrected codeword, the quarter-coordinates have even total, so their positive square sum is even and at least two. There is no energy or coordinate cutoff."))), DescribeRole.Theorem))));
}
