using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9RegularSparseMaskDataDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse masks for the regular order-ninety lift list",
        H("Sparse masks for the regular order-ninety lift list"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("regular-lift-records"),
                DeclarationHandle.Create(Module + ".records"),
                H("Thirty-two supports and their transverse masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The census of regular twelve-plus-three majority blocks gives the listed supports. Each record stores its axis and three-direction mask."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("regular-list-exclusion"),
                DeclarationHandle.Create(Module + ".listed_support_not_universal"),
                H("Exclusion of every listed support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed local tests are evaluated by the Lean kernel. Every listed support fails universal weighted sharpness under any coherent switching. The exhaustion of the signed orbit census is a separate mathematical obligation."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate"))]));
}
