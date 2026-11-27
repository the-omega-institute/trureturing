using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class AvatarCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avatar Compatibility", H("Avatar Compatibility"),
        Blocks(
            Paragraph(Text("Galois representations for all eigenforms of odd rank, by l-adic limits of seeds. Descent of the Galois representation along quadratic steps, replacing the patching lemma. Local-global compatibility of l-adic avatars of algebraic Hecke characters at all finite places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AvatarCompatibility.avatarCompatAt_of_stablyUnram"),
                H("avatarCompatAt_of_stablyUnram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a stably unramified CM field E, the ℓ-adic avatar μ of an algebraic character θ of type n satisfies the local clauses AvatarCompatAt (finite type, jumps, killing polynomials in degrees 0 and 1) at every place A above every finite place w.")))))));
}
