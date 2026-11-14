using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BishopMaximalPlacementGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/bonzini2008a146304");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Growth of maximal bishop placements", H("Growth of maximal bishop placements"), Blocks(
            Node("board", "The fixed-coordinate bishop graph", "bishopGraph",
                "The board is Fin n times Fin n. A square (x,y) has integer difference x-y and integer sum x+y. Distinct squares attack precisely when their differences or their sums agree. Placements are unlabelled subsets of this board, without identifying rotations or reflections.", DescribeRole.Definition),
            Node("count", "Inclusion-maximal placements", "count",
                "The count is the cardinality of all independent subsets maximal under inclusion, at every size. Maximal means that another bishop cannot be added; it does not mean maximum cardinality. The total convention at n=0 is outside the OEIS offset one.", DescribeRole.Definition),
            Node("claim", "The complete asymptotic assertion", "claim",
                "The assertion is the existence of a positive real C and a natural N at least one such that a(n) is at most C times n^(n-1) for every natural n at least N. Both the constant and the cutoff remain unrestricted.", DescribeRole.Definition),
            Node("cap", "The physical upper bound", "physical_cap",
                "For every n at least two, every counted maximal placement has at most 2n-2 bishops. Difference diagonals give an injective label map into 2n-1 possibilities. Both extreme diagonals are single corners with the same sum, so independence excludes at least one extreme. Removing that label gives the upper bound. The one-square board has its unique singleton maximal placement; a zero cap is not imposed there.", DescribeRole.Theorem),
            Node("dictionary", "The source cap preserves the native count", "source_family_card",
                "Filtering the native maximal placements by the physical cap for n at least two leaves their cardinality unchanged. The implication is vacuous at n=1, so the source boundary is preserved.", DescribeRole.Theorem),
            Node("lower", "Many distinct maximal completions", "count_lower_bound",
                "For every natural m, a(4m+1) is at least m^(6m). Within each diagonal parity, list signed difference lines by increasing length and select the fixed 3m lines at one-based positions m+1 through 4m. The jth selected line has at least m+j-1 squares, and each legal prefix leaves at least m choices. The two colors have disjoint sum labels as well as disjoint difference labels, so their choices combine on the same board. Every seed extends to an inclusion-maximal independent set by the finite maximal-extension theorem. Every selected line is already occupied. Independence prevents the extension from adding another square there, so restriction to the selected lines recovers the seed. Equivalently, a completed placement determines the chosen square on every prescribed difference line. Thus the map from the actual unordered seeds into maximal placements is injective.", DescribeRole.Theorem),
            Node("ratio", "Exponential divergence of the ratio", "ratio_lower_bound",
                "For every m at least 50, 4^m times (4m+1)^(4m) is at most a(4m+1). Indeed 4m+1 is at most 5m, and m squared is at least 2500, giving 4 times (5m)^4 at most m^6. Raising this inequality to m and using the seed bound proves the multiplied ratio estimate with positive denominators.", DescribeRole.Theorem),
            Node("refutation", "Failure of the Big-O bound", "result",
                "The complete asymptotic assertion is false. Given any positive real C and any cutoff N, choose m at least 50 and N with 4^m greater than C. Then n=4m+1 is beyond the cutoff and the ratio estimate gives a(n) greater than C times n^(n-1). This is an unbounded family of strict violations, independent of any finite table.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string name, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            Presentation(name), name is "bishopGraph" or "count" or "claim" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a146304-maximal-bishop-growth-refutation"),
                ResolutionKind.Refuted) : null);

    private static StatementSource Presentation(string name)
    {
        Formula m = V("m"), n = V("n"), c = V("C"), cutoff = V("N");
        Formula size = Add(Mul(D(4), m), D(1));
        Formula upper = Le(Call("count", n), Mul(c, Pow(n, Sub(n, D(1)))));
        Formula assertion = Ex("C", Real, And(Lt(D(0), c),
            Ex("N", Nat, And(Le(D(1), cutoff), All("n", Nat, Imp(Le(cutoff, n), upper))))));
        Formula? f = name switch
        {
            "claim" => Iff(Call("claim"), assertion),
            "count_lower_bound" => All("m", Nat, Le(Pow(m, Mul(D(6), m)), Call("count", size))),
            "ratio_lower_bound" => All("m", Nat, Imp(Le(D(5, 0), m), Le(Mul(Pow(D(4), m), Pow(size, Mul(D(4), m))), Call("count", size)))),
            "source_family_card" => All("n", Nat, Eq(Call("card", Call("sourceFamily", n)), Call("count", n))),
            "physical_cap" => All("n", Nat, Imp(Le(D(2), n), All("M", Call("Placement", n), Le(Call("card", Call("val", V("M"))), Sub(Mul(D(2), n), D(2)))))),
            "result" => Seq(Neg, Sp, Call("claim")),
            _ => null
        };
        return f is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(f));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
