using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayEnumeratorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayEnumerator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact full polynomial Golay weight enumerator.", H("Faithful finite enumeration"),
        Blocks(
            Describe.Lean(DescribeId.Create("packed-encoding"),
                DeclarationHandle.Create(Prefix + "packed_encode_identity"),
                H("Bitwise representation of the actual linear code"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Decoding bitwise XOR gives binary addition. The twelve literal packed generators decode to the actual polynomial-generator columns. Induction proves equality with the linear encoding for every message; the packed algorithm is not an assumed numerical oracle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("faithful-enumeration"),
                DeclarationHandle.Create(Prefix + "faithful_enumeration"),
                H("Every actual codeword exactly once"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two six-bit integers enumerate the entire twelve-coordinate message space bijectively. Encoding injectivity gives a unique pair for every actual codeword."))), DescribeRole.Theorem))));
}
