using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Hilbert90;

internal sealed class UnitaryHilbert90Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary Hilbert90", H("Unitary Hilbert90"),
        Blocks(
            Paragraph(Text("Unitary Hilbert 90 at level m and orthonormal frames over profinite rings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Hilbert90/UnitaryHilbert90.unitary_hilbert90_at_level"),
                H("unitary_hilbert90_at_level"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hilbert 90 for the unitary group at level m: under the hypotheses on O and τ of exists_fixed_orthonormal_frame, with m* = m and τ tame at level m, a unitary s ≡ 1 mod m of twisted norm 1 is g · τ(g)⁻¹ with g unitary, g ≡ 1 mod m.")))))));
}
