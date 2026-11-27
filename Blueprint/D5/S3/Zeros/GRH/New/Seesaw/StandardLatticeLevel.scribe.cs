using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class StandardLatticeLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Standard Lattice Level", H("Standard Lattice Level"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/StandardLatticeLevel.inclXFin_mem_Kf"),
                H("inclXFin_mem_Kf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Under Grading.SpansLattice, the inclusion U(X) → U(V) maps a congruence subgroup mod π into Kf; base case of the support bound.")))))));
}
