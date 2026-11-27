using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class ArtinDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Artin Defs", H("Artin Defs"),
        Blocks(
            Paragraph(Text("Pontryagin duality for the abelianisation of a profinite group; characters separate points. Definitions of algebraic Hecke characters and of the global Artin map.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/ArtinDefs.exists_hom_abelianLift_eq"),
                H("exists_hom_abelianLift_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Pontryagin duality for profinite G: if s maps a group X homomorphically to the additive maps from continuous characters of G to ℚ/ℤ, some homomorphism f : X → G^ab has χ(f(x)) = s(x)(χ) for all χ, x.")))))));
}
