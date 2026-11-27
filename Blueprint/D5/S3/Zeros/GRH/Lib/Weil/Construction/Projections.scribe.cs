using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class ProjectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projections", H("Projections"),
        Blocks(
            Paragraph(Text("Lattice vacuum projections at finite places and their interaction with the Weil action.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/Projections.omega_vacElem_sum"),
                H("omega_vacElem_sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For g in G_f, ω(g)vac equals Δ_f(g)|Δ_f(g)|⁻² times the sum of ϱ_f(gy)vac over coset representatives y of Ô^n ∩ g⁻¹Ô^n in Ô^n, where ϱ_f = Space.finHeisOp.")))))));
}
