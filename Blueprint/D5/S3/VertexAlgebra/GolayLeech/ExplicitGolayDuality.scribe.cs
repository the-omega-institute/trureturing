using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Golay-congruence lattice mathematics.",
        H("Exact integral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"),
                DeclarationHandle.Create(Prefix + "code_self_dual"), H("Actual self-duality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The twelve generator rows are mutually orthogonal in characteristic two. Injectivity gives dimension twelve, and the nondegenerate ambient dot product gives dimension twelve for the orthogonal complement. Inclusion and equal dimension prove equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-1"),
                DeclarationHandle.Create(Prefix + "code_cardinality"), H("Exactly 4096 words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linear encoding equivalence identifies the actual range with the full twelve-dimensional binary message space."))), DescribeRole.Theorem))));
}
