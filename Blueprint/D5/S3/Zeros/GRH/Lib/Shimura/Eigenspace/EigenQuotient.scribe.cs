using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Eigenspace;

internal sealed class EigenQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eigen Quotient", H("Eigen Quotient"),
        Blocks(
            Paragraph(Text("Largest Hecke eigen-quotient of cohomology: existence, continuity, crystallinity, killed Frobenius, weights.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Eigenspace/EigenQuotient.exists_word_kill_of_jump_eq_zero"),
                H("exists_word_kill_of_jump_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let θ cut r out of crystalline ρ_i (toGp Γ open, the T_s commuting with each other and with Γ), and η = γθ. If u is no jump of r at γ, some polynomial c with c(η) = 1 has c(T) killing the weight u vectors (HasHodgeTateWeight) of each ℂ_ℓ ⊗ V_i.")))))));
}
