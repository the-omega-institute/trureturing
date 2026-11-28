using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli;

internal sealed class FamilyFromPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Family From Points", H("Family From Points"),
        Blocks(
            Paragraph(Text("Closure of theta points is an abelian scheme with action and theta structure.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/FamilyFromPoints.exists_thetaFamily_of_points"),
                H("exists_thetaFamily_of_points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be reduced, locally Noetherian, embedded over R (Spec R → Spec O_E mono, β̄ − β and |T| units) by systems c lifting level coordinates of theta tori x_k at points η_k over Φ_{v₀}, finitely many dense. Under cl (IsCutOutAt) and cv, S carries a family modelled on x_k at η_k.")))))));
}
