using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class BlocksAndCocyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blocks And Cocycles", H("Blocks And Cocycles"),
        Blocks(
            Paragraph(Text("Cocycles obeying relations among u(g)-1, extension by Artin-Rees; blocks of a lift.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/BlocksAndCocycles.exists_graph_subrepresentation"),
                H("exists_graph_subrepresentation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("By Artin–Rees: a cocycle c mod a that obeys the relations among the u_x(g) − 1 is, for some k, the value at (u(g) − 1) + a^k v (any v) of an equivariant map defined on a subrepresentation; Y is its graph.")))))));
}
