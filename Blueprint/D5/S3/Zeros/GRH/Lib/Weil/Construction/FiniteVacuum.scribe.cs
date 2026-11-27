using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class FiniteVacuumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Vacuum", H("Finite Vacuum"),
        Blocks(
            Paragraph(Text("Self-dual lattice gives a vacuum for the finite Heisenberg group (lattice model).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteVacuum.latticeMeasure"),
                H("latticeMeasure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Haar measure on n-tuples of finite adeles of E that gives the lattice Ô^n mass one.")))))));
}
