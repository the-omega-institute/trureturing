using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class WeilOperatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weil Operators", H("Weil Operators"),
        Blocks(
            Paragraph(Text("Abstract Weil operators on vacuum coefficients: cocycle, unitarity, intertwining of Heisenberg action, continuity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/WeilOperators.weilOp_mul"),
                H("weilOp_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Cocycle relation for the Weil operators ω attached to a vacuum e and an action with cocycle c: if c(g,1) = 1 for all g, then ω(g)ω(h) = c(g,h)·ω(gh).")))))));
}
