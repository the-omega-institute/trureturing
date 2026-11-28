using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Trace;

internal sealed class BadShareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bad Share", H("Bad Share"),
        Blocks(
            Paragraph(Text("The bound bad_share_le for the share of bad types. Primitive labels: stable under scaling of roots; norm of a generator generates. A primitive cuspidal character has a cubic twist agreeing off irreducible characteristic polynomials.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Trace/BadShare.bad_share_le"),
                H("bad_share_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Bad share: take f fields of order q, 1 < r = |n| < q, M ≥ 1, (1+M+2r)/q ≤ ε ≤ 1, 2r(2r log q + 1)L ≤ f. For e the sum of tupleIdem over goodTuples M r, Re (1 − e)(1) ≤ fε + exp(−L).")))))));
}
