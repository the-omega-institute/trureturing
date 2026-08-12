using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class DiagonalCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Disp(Seq(
            F.Id("x"), Gt, D(0), Sp, Rightarrow, Sp,
            F.Id("W"), Open, F.Id("x"), Comma, F.Id("x"), Close,
            Sp, Eq, Sp, Frac,
            Grp(D(1)),
            Grp(
                D(1), Minus, Operatorname, Grp(F.Id("exp")),
                Open, Minus, Sqrt, Grp(D(5)), F.Id("x"), Close)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The two-face generating function collapses on the diagonal to a geometric series.",
            H("Diagonal Collapse of the Two-Face Generating Function"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("the-diagonal-partition-is-a-geometric-series"),
                    DeclarationHandle.Create(
                        "D5/S3/Analytic/DiagonalCollapse.diagonal_partition_collapse"),
                    H("The diagonal partition is a geometric series"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every positive real diagonal parameter, sum the two-face "
                            + "weight over all canonical nonadjacent Fibonacci words. Binet's "
                            + "formula turns the difference between the expansion and contraction "
                            + "powers into sqrt(5) times the decoded Fibonacci value. The canonical "
                            + "word equivalence then reindexes the sum by the natural numbers, where "
                            + "it is exactly the geometric series with ratio exp(-sqrt(5) x). The "
                            + "positivity hypothesis makes the convergence condition explicit; it "
                            + "was implicit in the source atom's analytic notation.")),
                        Paragraph(Text(
                            "The pinned library was searched first. It contains the canonical "
                            + "Zeckendorf equivalence, Binet's formula, and the real geometric-series "
                            + "summation theorem, but no declaration combining them into this "
                            + "diagonal identity. The proof is therefore a new composition of "
                            + "library results rather than a wrapper around an existing combined "
                            + "theorem. The numerical window check reported with the source atom is "
                            + "not needed because the deposited equality is exact."))),
                    DescribeRole.Theorem))));
    }
}
