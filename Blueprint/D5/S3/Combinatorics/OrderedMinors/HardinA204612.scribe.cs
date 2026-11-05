using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrderedMinors;

internal sealed class HardinA204612Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrderedMinors/HardinA204612.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardin2012a204612");
    private const string NameQuote = "OEIS A204612, NAME (unpaginated): \"Number of (n+1)X5 0..1 arrays with the determinants of 2X2 subblocks nondecreasing rightwards and downwards.\"";
    private const string FormulaQuote = "OEIS A204612, FORMULA (unpaginated): \"Empirical: a(n) = 18*a(n-1) -73*a(n-2) -256*a(n-3) +2060*a(n-4) -1216*a(n-5) -12612*a(n-6) +18224*a(n-7) +20992*a(n-8) -40064*a(n-9) -9984*a(n-10) +24576*a(n-11) for n>15\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-column ordered-minor array counts satisfy Hardin's eleven-term recurrence.",
        H("Hardin's recurrence for OEIS A204612"),
        Blocks(
            Node("minor", "The adjacent integer determinant", MinorBody(), true, true,
                NameQuote + " For A : Matrix (Fin (n + 1)) (Fin 5) (Fin 2), i : Fin n and j : Fin 4, minor A i j is the determinant over the integers of the adjacent block with top left corner (i,j). Fin.val gives the natural value of a binary entry, which is then cast to the integers. The boundary does not wrap."),
            Node("OrderedMinors", "Monotonicity in both directions", OrderedBody(), true, true,
                NameQuote + " Every row of adjacent determinants is Monotone in the column index, and every column of adjacent determinants is Monotone in the row index. Repeated rows and equal determinants are allowed."),
            Node("a", "The literal array count", CountBody(), true, true,
                NameQuote + " The integer a(n) is Nat.card of the subtype of the binary matrices satisfying OrderedMinors. Thus the count is defined from the arrays, independently of the recurrence. The source offset is 1,1; n = 0 is defined in Lean but does not occur in the asserted range."),
            Node("claim", "Hardin's empirical formula", Equal(V("claim"), Parenthesized(ClaimBody())), true, true,
                FormulaQuote + " The index n is natural, the strict threshold is 15 < n, and all eleven subtractions in the arguments are natural subtraction. The count is cast to the integers before the signed arithmetic on the right hand side."),
            Node("result", "The eleven-term recurrence", ClaimBody(), false, false,
                "Coding the two initial rows and all subsequent rows gives a labeled path on 68 boundary states. The literal array count equals the total of a power of the transition matrix applied to the initial multiplicities. A degree-eleven polynomial residual belongs to an invariant span of eleven paired boundary-bit differences whose total is zero. Every further transition power preserves that span, so taking totals yields the displayed identity at every n > 15. This proves the source formula; minimal order, a smaller threshold and larger widths are separate questions.",
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hardin-a204612"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        bool definition, bool literature, string prose,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hardina204612-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem,
            openProblemResolutionClaim: resolution);

    private static Formula V(string value) => F.Id(value);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula IntType() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Add(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
    private static Formula Sub(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Subtract, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) => new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula ArrayType(Formula n) => Call("Matrix", Fin(Add(n, D(1))), Fin(D(5)), Fin(D(2)));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, IntType()));
    private static Formula Entry(Formula row, Formula column) => Cast(Call("val", App(V("A"), row, column)));
    private static Formula MinorBody()
    {
        var i = V("i"); var j = V("j");
        var top = App(Qualified("Fin", "castSucc"), i); var bottom = App(Qualified("Fin", "succ"), i);
        var left = App(Qualified("Fin", "castSucc"), j); var right = App(Qualified("Fin", "succ"), j);
        var matrix = Seq(Begin, Grp(V("pmatrix")), Entry(top, left), Amp, Entry(top, right), RowBreak,
            Entry(bottom, left), Amp, Entry(bottom, right), End, Grp(V("pmatrix")));
        return All("n", NatType(), All("A", ArrayType(V("n")), All("i", Fin(V("n")), All("j", Fin(D(4)),
            Equal(Call("minor", V("A"), i, j), App(Qualified("Matrix", "det"), matrix))))));
    }
    private static Formula OrderedBody()
    {
        var row = All("i", Fin(V("n")), Call("Monotone", Call("minor", V("A"), V("i"))));
        var column = All("j", Fin(D(4)), Call("Monotone", Parenthesized(Seq(
            V("i"), Colon, Sp, Fin(V("n")), Sp, Mapsto, Sp, Call("minor", V("A"), V("i"), V("j"))))));
        return All("n", NatType(), All("A", ArrayType(V("n")), Equal(Call("OrderedMinors", V("A")),
            new Formula.Logic(Parenthesized(row), FormulaLogicOperator.And, Parenthesized(column)))));
    }
    private static Formula CountBody()
    {
        var subtype = Seq(OpenBrace, V("A"), Colon, Sp, ArrayType(V("n")), Sp, Bar, Sp,
            Call("OrderedMinors", V("A")), CloseBrace);
        return All("n", NatType(), Equal(Call("a", V("n")), Cast(App(Qualified("Nat", "card"), subtype))));
    }
    private static Formula Term(Formula coefficient, Formula lag) => Mul(coefficient, Call("a", Sub(V("n"), lag)));
    private static Formula ClaimBody()
    {
        var rhs = Sub(Term(D(1,8), D(1)), Term(D(7,3), D(2)));
        rhs = Sub(rhs, Term(D(2,5,6), D(3)));
        rhs = Add(rhs, Term(D(2,0,6,0), D(4)));
        rhs = Sub(rhs, Term(D(1,2,1,6), D(5)));
        rhs = Sub(rhs, Term(D(1,2,6,1,2), D(6)));
        rhs = Add(rhs, Term(D(1,8,2,2,4), D(7)));
        rhs = Add(rhs, Term(D(2,0,9,9,2), D(8)));
        rhs = Sub(rhs, Term(D(4,0,0,6,4), D(9)));
        rhs = Sub(rhs, Term(D(9,9,8,4), D(1,0)));
        rhs = Add(rhs, Term(D(2,4,5,7,6), D(1,1)));
        return All("n", NatType(), Seq(Parenthesized(new Formula.Relation(D(1,5), FormulaRelationOperator.LessThan, V("n"))),
            Sp, Rightarrow, Sp, Equal(Call("a", V("n")), rhs)));
    }
}
