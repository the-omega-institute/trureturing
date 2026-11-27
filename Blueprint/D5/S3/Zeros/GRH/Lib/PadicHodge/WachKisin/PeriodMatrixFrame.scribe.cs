using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin;

internal sealed class PeriodMatrixFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period Matrix Frame", H("Period Matrix Frame"),
        Blocks(
            Paragraph(Text("Existence of a finite-height Kisin frame in A_inf for a crystalline period matrix.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixFrame.exists_frame"),
                H("exists_frame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a period matrix U for (h, v) there are Q, L over A_inf, Z over S_B, Z' over B^+, B over S with QL = τ^h, UZ = E^hQ, Z'Z = E^h, φQ = vQB, and gZ ∈ Z·M_d(A_inf) for all g fixing Λ and θ(z).")))))));
}
