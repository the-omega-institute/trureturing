using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class BorderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bordering", H("Bordering"),
        Blocks(
            Paragraph(Text("Leading terms in one row, bordering of minors, recursion for alternants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Bordering.exists_bordering"),
                H("exists_bordering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Bordering: if γ interlaces the columns' weight at x's colour, some heights k have weight smaller by γ, and each filling I avoiding row x lifts to K, with |γ| more entries x, whose minor product has leading term y_x^γ times I's over every ring.")))))));
}
