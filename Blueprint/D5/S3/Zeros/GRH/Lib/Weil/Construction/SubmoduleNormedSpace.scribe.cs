using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class SubmoduleNormedSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Submodule Normed Space", H("Submodule Normed Space"),
        Blocks(
            Paragraph(Text("Elementary identities for the Heisenberg bicharacter and the vacuum function. Heisenberg representation twisted by a group element preserving the cocycle. Shortcut instance: a complex subspace of a normed space is normed.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/SubmoduleNormedSpace.moveBy"),
                H("moveBy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a Heisenberg representation ρ, an action A of G on W preserving β, and g in G, the Heisenberg representation x ↦ ρ(gx) on the same space.")))))));
}
