using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Topology;

internal sealed class LocalDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Defs", H("Local Defs"),
        Blocks(
            Paragraph(Text("Schwartz-Bruhat functions, products of local fields, tame and additive characters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Topology/LocalDefs.HasIntegralConductor"),
                H("HasIntegralConductor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The additive character ψ has conductor O: ψ is trivial on tO exactly when t lies in O.")))))));
}
