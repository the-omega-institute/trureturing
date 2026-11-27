using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Limit;

internal sealed class LocalLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Limit", H("Local Limit"),
        Blocks(
            Paragraph(Text("Uniform limits of traces keep crystallinity, Hodge-Tate weights and killing polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/LocalLimit.local_clauses_of_trace_limit"),
                H("local_clauses_of_trace_limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let tr r (r continuous, with IsTraceNondeg) be a uniform limit of combinations of traces of continuous representations unramified or crystalline at A, finitely many in all or all with jumps J. So is r; jump multiplicities and, under coefficientwise uniform convergence, killing polynomials of bounded degree pass to r.")))))));
}
