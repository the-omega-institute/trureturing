using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class EquivariantUnitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant Units", H("Equivariant Units"),
        Blocks(
            Paragraph(Text("Herbrand's equivariant S-unit theorem: units plus Z span permutation module of places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/EquivariantUnits.dirichlet_fixedSUnits"),
                H("dirichlet_fixedSUnits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Equivariant Dirichlet theorem: with X the places above N∞ of the field of Q, its N-units E are finitely generated, rank(E × ℤ) ≤ #X, and there are ℝ-linearly independent additive maps Λ_z : E × ℤ → ℝ (z ∈ X) with Λ_z(g⁻¹y) = Λ_{gz}(y).")))))));
}
