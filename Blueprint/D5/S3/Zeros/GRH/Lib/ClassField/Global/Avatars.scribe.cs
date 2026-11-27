using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Global;

internal sealed class AvatarsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avatars", H("Avatars"),
        Blocks(
            Paragraph(Text("Existence theorem of class field theory for totally complex fields, by Kummer counting. p-adic avatar of algebraic Hecke characters over totally complex fields; values off p.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Global/Avatars.avatar_localArtin"),
                H("avatar_localArtin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A lie over v, with v ∤ p or n_σ = 0 whenever ιℓ∘σ induces v. If g in the decomposition group D of A has class Art_v(x) in D^ab, the avatar of (θ, n) at g is ιℓ(θ(x)), x an idele at v.")))))));
}
