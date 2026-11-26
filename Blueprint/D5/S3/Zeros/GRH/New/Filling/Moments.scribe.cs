using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class MomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moments", H("Moments"),
        Blocks(
            Paragraph(Text("Trace of a small central projection on the Bessel-subgroup terms is small. Sharp bound for the second moment over elements fixing vectors with unit minors. Moment bounds for the Poincaré series and spread of translates modulo any subspace.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/Moments.exists_translate_finrank_comap_le"),
                H("exists_translate_finrank_comap_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Filling: let ρ be unitary, ⟨ρ(s)Qe_y, Qe_x⟩ = c·(amplitude sums), c > 0, R = ρ(∏g_i) for central idempotents with Re(1−g_i)(1) ≤ b⁻⁸/2, rank R ≤ |𝖦|·deg·mass. Each subspace F of im R, of share φ, has an s with dim (Rρ(s)Q)⁻¹F ≤ ½(1 + φ + 19b⁻⁴)D_c.")))))));
}
