using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Transfer;

internal sealed class PELDataExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "PEL Data Existence", H("PEL Data Existence"),
        Blocks(
            Paragraph(Text("Regular test function with cuspidal type that does not kill the given vector. Eigensystem of a definite form occurs in each Hodge weight for signature (1,n-1). Lagrangians exist; PEL data with odd theta group, good at the safe places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Transfer/PELDataExistence.exists_pel"),
                H("exists_pel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For E ⊇ ℚ(√−d) stably unramified, σ: E → ℂ, finitely many places B: some CM type with Φ_{v₀} = σ, other Φ_v ≠ σ on ℚ(√−d), and N prime to B give at each level 0 ≠ 𝔑 ∈ (N) PEL data with signs, β = (1 + √−d)/2, good at safe places.")))))));
}
