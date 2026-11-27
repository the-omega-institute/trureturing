using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli;

internal sealed class FlatClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat Closure", H("Flat Closure"),
        Blocks(
            Paragraph(Text("Schematic density of points passes to stalks and to fibre products. Coordinates locally regular combinations of a linear system form a system of same class. Closure of theta points over the base is flat with reduced fibres.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/FlatClosure.exists_flat_closure"),
                H("exists_flat_closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be reduced, finitely many of the η n dense, r > 1; assume IsCutDegree, and IsCutOutAt at η n for the image of θ n and at a geometric specialisation of every point. Then some flat closed A ⊂ ℙ^J_S has reduced fibres over η n, in which the θ n z are dense, and at such specialisations.")))))));
}
