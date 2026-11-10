using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233257StripDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip";
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233257");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed form and generating function for the two-row antidiagonal strip.",
        H("The normalized two-row antidiagonal strip"),
        Blocks(
            Paragraph(Text("The strip has horizontal bonds in both rows and a bond from the lower "
                + "cell of a column to the upper cell of the next column. Bonded colours differ "
                + "and do not sum to five. The first cell is zero. Row-major order puts the whole "
                + "upper row before the lower row. Normalization is the predicate "
                + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.normal. "
                + "The empty coefficient is zero. All formula "
                + "names are full Lean names; Fin.val and Int.ofNat display the relevant coercions.")),
            Node("Legal", "Literal bond and normalization predicate", LegalFormula(), false),
            Node("a", "Literal filtered count", CountFormula(), false),
            Node("finite_certificate", "The empty and one-column coefficients", InitialFormula(), true),
            Node("closed_form", "Barker's closed form", ClosedFormula(), true),
            Node("recurrence", "Hardin's integer recurrence", RecurrenceFormula(), true),
            Resolution("result", "Barker's generating function with the closed form and recurrence",
                And(SeriesFormula(), And(ClosedFormula(), RecurrenceFormula()))),
            Paragraph(Text("The pair-label map D5.S3.Observer.Separation.BooleanRankThreeK4.beta "
                + "turns every bond into label inequality. For width n+2, the last-column transfer "
                + "distinguishes equal and unequal labels within a column. Its matrix has rows "
                + "(2,2) and (1,1), and its initial weights are (12,12). These weights form a left "
                + "eigenvector with eigenvalue three. Mathlib's eigenvector power theorem gives "
                + "24 times 3 to the power n proper three-label patterns. If a label is omitted, "
                + "the three-label bond constraints force every column to be constant. Replicating "
                + "the upper row four times gives an array to which "
                + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.two_label_classification "
                + "applies. Restricting its alternating pattern and identifying the lower row "
                + "gives exactly six two-label patterns. "
                + "The frozen canonical_pattern_card and normalized_card theorems of "
                + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical give four times "
                + "3 to the power n canonical patterns, one of them with two labels. Their lift "
                + "weights give the closed form. Expanding the two geometric factors gives the "
                + "integer recurrence and the coefficient identity. Hardin authored the sequence "
                + "and empirical recurrence; Barker stated the closed form and generating function.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static DocumentBlock Resolution(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233257"), ResolutionKind.Proved));

    private static Formula N => Q("Nat");
    private static Formula Z => Q("Int");
    private static Formula Cells(Formula n) => Seq(Fin(D(2)), Times, Fin(n));
    private static Formula Arrays(Formula n) => Arrow(Parenthesized(Cells(n)), Fin(D(6)));
    private static Formula Pair(Formula r, Formula j) => Parenthesized(Seq(r, Comma, Sp, j));
    private static Formula At(Formula a, Formula r, Formula j) => App(a, Pair(r, j));
    private static Formula R(int n) => Typed(Num(n), Fin(D(2)));
    private static Formula Next(Formula j, Formula h) => Call("Fin.mk", Add(Val(j), D(1)), h);
    private static Formula Bond(Formula x, Formula y) =>
        And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)));

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j"); var h = V("h"); var r = V("r");
        var first = Ex("j", Fin(n), And(Eq(Val(j), D(0)), Eq(At(a, R(0), j), Colour(0))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n), And(
            All("r", Fin(D(2)), Bond(At(a, r, j), At(a, r, Next(j, h)))),
            Bond(At(a, R(1), j), At(a, R(0), Next(j, h))))));
        return All("n", N, All("A", Arrays(n), Eq(Own("Legal", a),
            Parenthesized(And(first, And(bonds,
                Call("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n");
        var filter = Call("Finset.filter", Fn("A", Arrays(n), Own("Legal", V("A"))),
            Typed(Q("Finset.univ"), Call("Finset", Arrays(n))));
        return All("n", N, Eq(Own("a", n), Call("Finset.card", filter)));
    }

    private static Formula InitialFormula() =>
        And(Eq(Own("a", D(0)), D(0)), Eq(Own("a", D(1)), D(3)));

    private static Formula ClosedFormula()
    {
        var n = V("n");
        return All("n", N, Eq(Mul(D(9), Own("a", Add(n, D(2)))),
            Mul(Power(D(2), Add(Mul(D(2), n), D(1))),
                Add(Mul(D(4), Power(D(3), Add(n, D(2)))), D(9)))));
    }

    private static Formula Aint(Formula n) => Call("Int.ofNat", Own("a", n));
    private static Formula RecurrenceFormula()
    {
        var n = V("n");
        return All("n", N, Eq(Aint(Add(n, D(4))),
            Sub(Mul(Typed(D(1,6), Z), Aint(Add(n, D(3)))),
                Mul(Typed(D(4,8), Z), Aint(Add(n, D(2)))))));
    }

    private static Formula SeriesFormula()
    {
        var ps = Call("PowerSeries", Z);
        var x = Typed(Q("PowerSeries.X"), ps);
        Formula C(int n) => Typed(Num(n), ps);
        var series = Typed(Call("PowerSeries.mk", Fn("n", N, Aint(V("n")))), ps);
        return Eq(Mul(Mul(Sub(C(1), Mul(C(4), x)), Sub(C(1), Mul(C(12), x))), series),
            Mul(x, Add(Sub(C(3), Mul(C(38), x)), Mul(C(88), Power(x, D(2))))));
    }

    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(Owner + "." + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Colour(int n) => Typed(Num(n), Fin(D(6)));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
