using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class LatticeAndTorsionDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice And Torsion Defs", H("Lattice And Torsion Defs"),
        Blocks(
            Paragraph(Text("Lattice basis gradedLatticeBasis, admissible combinations of translates with controlled denominators and size.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/LatticeAndTorsionDefs.IsSplitSquarefree"),
                H("IsSplitSquarefree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("N = π·π̄ for the finite idele π, which is a uniformiser at the places of P and a unit elsewhere, and P is disjoint from its conjugate.")))))));
}
