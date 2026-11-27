using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Unitary;

internal sealed class SpaceDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Space Defs", H("Space Defs"),
        Blocks(
            Paragraph(Text("Adelic unitary groups, split places, compact levels, framed hermitian spaces, lattices, masses.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceDefs.volume_Kf"),
                H("volume_Kf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the chosen Haar measure on the finite adelic unitary group G_f, the subgroup K_0 = G_f ∩ GL_n(Ô) has volume 1.")))))));
}
