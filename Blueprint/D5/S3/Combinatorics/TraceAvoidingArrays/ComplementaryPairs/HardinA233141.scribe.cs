using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233141Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233141";
    private const string Note = "D5/L/Automata/hardin2013a233141";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for normalized six-colour two-column arrays.",
        H("Complementary exclusion on two columns"),
        Blocks(
            Describe.Lean(DescribeId.Create("legal"), DeclarationHandle.Create(Owner + ".Legal"),
                H("Literal legality"), StatementSource.FromAuthor(Disp(LegalFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All entries are in 0 through 5. A bond forbids precisely a sum of five, "
                    + "so equal adjacent colours are permitted. The constrained edges are horizontal, vertical, "
                    + "and antidiagonal from the right cell of one row to the left cell of the next. "
                    + "The first cell must exist and equal zero. Every occurrence of 2, 3 or 4 has a strictly "
                    + "earlier 1, and every 3 has a strictly earlier 2, using the rank 2i+j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidablelegal"), DeclarationHandle.Create(Owner + ".instDecidableLegal"),
                H("Deciding literal legality"), StatementSource.FromAuthor(Disp(DecisionFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The deciding instance combines the four finite clauses in the legality predicate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Owner + ".a"),
                H("Filtered array count"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every function on the indicated finite cell domain is included in the filter's universe. "
                    + "The anchor fails at height zero, giving a(0)=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Barker's complete generating function"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("The width_counting_bridge of HardinA233251TriangleStrip identifies the literal count "
                        + "with the continuation transfer for width two. The two first-use flags and two row colours "
                        + "give 144 states. The integer transfer matrix has an entry one exactly when a legal next row "
                        + "updates the flags and row colours to the destination state, and zero otherwise.")),
                    Paragraph(Text("The six certified continuation vectors establish a degree-five relation after one "
                        + "transfer step on every state. TransferMatrix.scalarRelationShift propagates it to all "
                        + "subsequent continuations. The first six positive counts are 2, 16, 225, 3727, 65120 and "
                        + "1158334. The recurrence for index at least six has signed coefficients "
                        + "25, -134, 134, -25, 1 for lags one through five, respectively. Coefficient comparison, including index zero, "
                        + "gives the polynomial product identity. The denominator has constant coefficient one, "
                        + "allowing its inverse in the rational formal power series ring."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233141"),
                    ResolutionKind.Proved)))));

    private static Formula LegalFormula() => All("n", V("Nat"), All("A", ArrayType(V("n")),
        Iff(Call("Legal", V("A")), LegalBody())));

    private static Formula LegalBody()
    {
        var n = V("n");
        var i = V("i");
        var rows = Call("Fin", n);
        Formula Cell(Formula r, byte c) => App(V("A"), Pair(r, D(c)));
        Formula Bond(Formula a, Formula b) => Ne(Add(Call("Fin.val", a), Call("Fin.val", b)), D(5));
        var first = Ex("i", rows, And(Eq(Call("Fin.val", i), D(0)), Eq(Cell(i, 0), D(0))));
        var horizontal = All("i", rows, Bond(Cell(i, 0), Cell(i, 1)));
        var next = Call("Fin.mk", Add(Call("Fin.val", i), D(1)), V("h"));
        var between = All("i", rows, All("h", Lt(Add(Call("Fin.val", i), D(1)), n),
            And(Bond(Cell(i, 0), Cell(next, 0)), And(Bond(Cell(i, 1), Cell(next, 1)),
                Bond(Cell(i, 1), Cell(next, 0))))));
        var cells = CellType(n);
        var p = V("p");
        var q = V("q");
        Formula Rank(Formula c) => Add(Mul(D(2), Call("Fin.val", Call("Prod.fst", c))),
            Call("Fin.val", Call("Prod.snd", c)));
        Formula Is(byte colour) => Eq(App(V("A"), p), D(colour));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(V("A"), q), D(colour))));
        var normal = All("p", cells, And(Imp(Or(Is(2), Or(Is(3), Is(4))), Earlier(1)),
            Imp(Is(3), Earlier(2))));
        return And(first, And(horizontal, And(between, normal)));
    }

    private static Formula DecisionFormula() => All("n", V("Nat"), All("A", ArrayType(V("n")),
        Eq(Parenthesized(Seq(Call("instDecidableLegal", V("A")), Colon, Sp,
                Call("Decidable", Call("Legal", V("A"))))),
            Call("inferInstanceAs", Call("Decidable", Parenthesized(LegalBody()))))));

    private static Formula Count(Formula n)
    {
        var predicate = Seq(LambdaLower, Sp, V("A"), Colon, Sp, ArrayType(n), Sp, Mapsto, Sp, Call("Legal", V("A")));
        return Call("Finset.card", Call("Finset.filter", predicate, Name("Finset.univ")));
    }

    private static Formula CountFormula() => All("n", V("Nat"), Eq(Call("a", V("n")), Count(V("n"))));

    private static Formula ResultFormula()
    {
        var x = V("X");
        var n = V("n");
        Formula XP(byte k) => new Formula.Power(x, D(k));
        var numerator = Mul(x, Add(Sub(Add(Sub(D(2), Mul(D(3,4), x)),
            Mul(D(9,3), XP(2))), Mul(D(2,2), XP(3))), XP(4)));
        var denominator = Mul(Mul(Sub(D(1), x), Add(Sub(D(1), Mul(D(1,8), x)), XP(2))),
            Add(Sub(D(1), Mul(D(6), x)), XP(2)));
        var series = Call("PowerSeries.mk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp, Mapsto, Sp,
            Parenthesized(Seq(Count(n), Colon, Sp, V("Rat")))));
        return Seq(Eq(series, Mul(numerator, new Formula.Power(Parenthesized(denominator), Seq(Minus, D(1))))),
            Sp, Name("in"), Sp, Call("PowerSeries", V("Rat")));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { V(part) } : new[] { Dot, V(part) }).ToArray()));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula CellType(Formula n) => Parenthesized(Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", D(2))));
    private static Formula ArrayType(Formula n) => Seq(CellType(n), Sp, To, Sp, Call("Fin", D(6)));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(a, Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
