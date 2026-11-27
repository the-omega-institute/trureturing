using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class BallModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ball Model", H("Ball Model"),
        Blocks(
            Paragraph(Text("Ball model for signature (1,n-1): periods, polarisation, linearised action at fixed points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/BallModel.exists_ball_family"),
                H("exists_ball_family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Some analytic family, parametrising points A(q) with A(0) = o, meets every point with frame o.x. If z : o·(g,α) ≅ o at level K(𝔑), z separable, o.reflection = eigenReflection True z μ, then z : A(q)·(g,α) ≅ A(Kq) near 0, K linear, localTerm(t) = localTerm(0)·det(1 − tK).")))))));
}
