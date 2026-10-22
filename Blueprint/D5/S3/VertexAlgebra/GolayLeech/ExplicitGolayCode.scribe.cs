using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Golay-congruence lattice mathematics.",
        H("Exact integral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"),
                DeclarationHandle.Create(Prefix + "polynomial_generator_certificate"), H("Exact polynomial generator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal generator matrix equals the degree-below-twelve cyclic polynomial construction with exponents 0,1,5,6,7,9,11. Each shifted polynomial has odd weight seven, so its twenty-fourth parity coordinate is one. Every generator equality is checked in the kernel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-1"),
                DeclarationHandle.Create(Prefix + "encode_injective"), H("No duplicate codewords"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The leading twelve coordinates form a triangular matrix with unit diagonal. Its determinant and injectivity identify all messages faithfully."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"),
                DeclarationHandle.Create(Prefix + "code_contains_all_ones"), H("The carry word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An explicit message produces the all-ones word, which is needed when two odd lattice vectors are added."))), DescribeRole.Theorem))));
}
