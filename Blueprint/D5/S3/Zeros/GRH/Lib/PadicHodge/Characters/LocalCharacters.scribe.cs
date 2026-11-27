using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Characters;

internal sealed class LocalCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Characters", H("Local Characters"),
        Blocks(
            Paragraph(Text("Local behaviour of l-adic avatars and of characters with finite inertia image.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/LocalCharacters.sphericalClause_of_unramified"),
                H("sphericalClause_of_unramified"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If AvatarCompatAt holds at w and θ is unramified at w, then at every A over w its ℓ-adic avatar is unramified (crystalline above ℓ), has jump −n(ι⁻¹τ) at τ, and X − ιθ_w(ϖ) kills every geometric Frobenius.")))))));
}
