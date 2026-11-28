using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class AdmissibleCombDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible Comb", H("Admissible Comb"),
        Blocks(
            Paragraph(Text("Calculus of finite combinations tracking support, denominator and size of conjugates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/AdmissibleComb.smul_mem"),
                H("smul_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let z be a combination (IsAdmissibleComb) of the v x, x ∈ A, with coefficients integral away from n up to the denominator d; l a prime not dividing n, ι : ℂ → ℂ_l. Then dz lies in every module over ι⁻¹(𝒪_{ℂ_l}) containing all v x.")))))));
}
