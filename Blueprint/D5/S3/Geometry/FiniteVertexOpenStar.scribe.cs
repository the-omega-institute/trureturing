using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteVertexOpenStarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteVertexOpenStar.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative open stars contract through actual face coordinates.",
        H("Based contractions of finite relative open vertex stars"),
        Blocks(
            Node("star", "star", "The relative open star",
                "For a pre-abstract simplicial complex M on a finite vertex type V, the star at v is the subspace of the actual coordinate realization on which coordinate v is strictly positive. No purity or link condition is assumed.", DescribeRole.Definition),
            Node("open", "isOpen_star", "The star is relatively open",
                "The coordinate evaluation is continuous, so its inverse image of the strictly positive real half-line is open in the realization. This openness assertion does not require a Fintype instance.", DescribeRole.Theorem),
            Node("vertex", "vertex_mem_star", "The realized vertex belongs to its star",
                "A singleton face at v supplies the actual coordinate vertex, whose v coordinate is one. This assertion is used by the based contraction and the finite bouquet cover.", DescribeRole.Theorem),
            Node("contraction", "contraction", "A contraction fixing the chosen vertex",
                "For every singleton face at v, the actual star has a jointly continuous homotopy relative to that vertex from its identity map to the constant vertex map. At time t the vector is (1-t)x+t e_v. Positivity of x_v forces every face witnessing x to contain v, so convexity keeps the whole segment in the same face. Its v coordinate stays positive, including t=1. Finite-coordinate continuity and the displayed formula prove the fixed-vertex condition. The construction consumes FiniteVertexCylinder.vertexPoint and the existing face-simplex coordinate description.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
