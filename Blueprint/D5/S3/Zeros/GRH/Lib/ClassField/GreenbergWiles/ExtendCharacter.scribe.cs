using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class ExtendCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extend Character", H("Extend Character"),
        Blocks(
            Paragraph(Text("Herbrand-type index; counting equivariant maps from a lattice to a projective module. Tate's index formula for the Herbrand quotient of a prime-order action.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/ExtendCharacter.exists_monoidHom_extend"),
                H("exists_monoidHom_extend"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let f : A → G and θ : A → C be homomorphisms of abelian groups, C divisible, H a subgroup of G. If θ is trivial on f⁻¹(H), some homomorphism χ : G → C kills H and has χ∘f = θ.")))))));
}
