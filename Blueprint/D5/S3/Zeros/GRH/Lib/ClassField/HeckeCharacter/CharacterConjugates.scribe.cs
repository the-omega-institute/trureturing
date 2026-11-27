using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class CharacterConjugatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character Conjugates", H("Character Conjugates"),
        Blocks(
            Paragraph(Text("Existence, finiteness and algebraicity of tame algebraic characters of the norm-one torus. p-adic absolute value of an algebraic Hecke character is given by its weights. Conjugates of algebraic characters: modulus one, permuted weight, conjugated tame part.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharacterConjugates.exists_conj"),
                H("exists_conj"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let μ have weight e and tame part ψ, and let σ ∈ Aut ℂ permute the CM type: σ∘Φ_v = Φ_{p(v)}. Then some ν has weight e∘p⁻¹, tame part σ∘ψ, and ν(u) = σ(μ(u)) whenever u has archimedean component 1.")))))));
}
