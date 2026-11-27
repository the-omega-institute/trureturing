using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class KatzDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Katz Divisibility", H("Katz Divisibility"),
        Blocks(
            Paragraph(Text("Sharpness of Katz's divisibility, by a multiplicative inequality between jets.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/KatzDivisibility.katz_divisibility_limit"),
                H("katz_divisibility_limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A limit to Katz's divisibility of jets (superadditivity). For d a prime ≡ 7 mod 8, every prime p, ring map ι : ℂ → ℂ_p and n, some f ∈ 𝔬[[φ]] has |f⁽ⁿ⁾(0)|_p ≥ p^{(ρ_p − 1/(p−1))n}.")))))));
}
