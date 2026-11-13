using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class MarkeyFiveSiteGrowthDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/MarkeyFiveSiteGrowthDifference.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/shannon2024markey2026hexgrowth");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Markey five-site growth differs from the Shannon vertex count by 4*n+7.",
        H("MarkeyFiveSiteGrowthDifference"),
        Blocks(
            Entry("markeya400701-claim", "MarkeyA400701.claim", Formula0(), "OEIS A400701 revision 30, NAME (unpaginated), verbatim: “Start with a set of five adjacent collinear points in a hexagonal lattice. Every iteration, add to the set the points in the lattice which are adjacent to at least two points already in the set. This sequence gives the number of points in the set after n iterations.” FORMULA, verbatim: “Conjectured: For n > 1: a(n) = A374338(n) + 4*n + 7.” The lattice has six unit directions. Both counts use the same natural iteration index.", DescribeRole.Definition, true),
            Entry("markeya400701-result", "MarkeyA400701.result", Formula1(), "The five-site count exceeds the two-site circle count by 4*n+7 at every iteration n>1.", DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, Formula formula, string prose, DescribeRole role, bool literature) =>
        Describe.Lean(DescribeId.Create("hexgrowth-" + id), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(name), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Qualified(params string[] names) => Seq(names.Select((name, i) =>
        i == 0 ? Named(name) : Seq(Dot, Named(name))).ToArray());
    private static Formula Formula0() => Disp(Seq(Qualified("MarkeyA400701", "claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Qualified("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(Qualified("Fin"), Sp, new Formula.Number(2))))))), Sp, Comma, Sp, F.Id("a"), Sp, Neq, Sp, F.Id("b"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, new Formula.Number(1), Sp, Lt, Sp, F.Id("n"), Sp, To, Sp, Qualified("MarkeyA400701", "latticeCount"), Sp, F.Id("n"), Sp, F.Eq, Sp, Qualified("ShannonA374338", "vertexCount"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("n"), Sp, Plus, Sp, new Formula.Number(4), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, new Formula.Number(7)))));
    private static Formula Formula1() => Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Parenthesized(Seq(Qualified("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(Qualified("Fin"), Sp, new Formula.Number(2))))))), Sp, Comma, Sp, F.Id("a"), Sp, Neq, Sp, F.Id("b"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, new Formula.Number(1), Sp, Lt, Sp, F.Id("n"), Sp, To, Sp, Qualified("MarkeyA400701", "latticeCount"), Sp, F.Id("n"), Sp, F.Eq, Sp, Qualified("ShannonA374338", "vertexCount"), Sp, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("n"), Sp, Plus, Sp, new Formula.Number(4), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, new Formula.Number(7)));
}
