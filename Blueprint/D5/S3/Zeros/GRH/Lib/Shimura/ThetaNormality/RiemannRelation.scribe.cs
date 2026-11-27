using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaNormality;

internal sealed class RiemannRelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann Relation", H("Riemann Relation"),
        Blocks(
            Paragraph(Text("Riemann's theta relation; largest theta constants; reduction cut out by level points.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/RiemannRelation.isCutOutAt_reduction"),
                H("isCutOutAt_reduction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the theta torus x satisfy HasGoodReduction for v, with residue field k. If the N_l have at t the reduced theta vectors of the level points as coordinates, then IsCutOutAt holds at t for the reductions of all theta vectors (θ_s(z))_s.")))))));
}
