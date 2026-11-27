using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class PeriodMatrixBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period Matrix Basis", H("Period Matrix Basis"),
        Blocks(
            Paragraph(Text("Kisin lattice of a period matrix is free and dense up to p-powers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixBasis.exists_basis"),
                H("exists_basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a period matrix U there are Q over A_inf with det Q ≠ 0 and Z over S_B with UZ = E^h Q, such that Uy = E^h x, y over S_B, gives x in QS^d, and for any y over B^+, δ ∣ lQ and p ∤ δ give δ ∣ l·x.")))))));
}
