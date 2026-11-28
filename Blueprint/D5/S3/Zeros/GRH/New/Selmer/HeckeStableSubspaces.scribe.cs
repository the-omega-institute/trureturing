using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class HeckeStableSubspacesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Stable Subspaces", H("Hecke Stable Subspaces"),
        Blocks(
            Paragraph(Text("the auxiliary pairs have apt labels; representations attached to eigenforms are conjugate self-dual, and local conditions pass to the conjugate place; a Hecke-stable space of forms has a Hecke-stable complement and is spanned by its isotypic vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/HeckeStableSubspaces.le_of_isotypic_mem"),
                H("le_of_isotypic_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A space Z of forms stable under all Hecke polynomials off the level lies in N if its nonzero isotypic vectors do.")))))));
}
