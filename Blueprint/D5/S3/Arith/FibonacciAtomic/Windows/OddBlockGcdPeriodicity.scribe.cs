using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Windows;

internal sealed class OddBlockGcdPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mbirikaspilker2023oddgcd");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both infinite-shift Gibonacci window gcds are periodic on positive odd lengths for every integer seed pair.",
        H("Joint Odd-Length Gibonacci GCD Periodicity"),
        Blocks(
            Paragraph(Text("All seed values a,b,c and divisors d are integers. Indices n,t,k,j and periods P are natural numbers, including zero. G(a,b,n), U(a,b,t,k), W(a,b,t,k), A(a,b,k) and B(a,b,k) denote the five definitions below. The natural range(k) is the set of indices i with 0 <= i < k; in particular range(0) is empty.")),
            Node("g", "The exact seeded recurrence", GFormula(),
                "The map step sends (x,y) to (y,x+y). The first coordinate of its n-fold iterate from (a,b) is G(a,b,n). Its initial values are a,b and its recurrence is G(n+2)=G(n)+G(n+1). The result also identifies it with every integer sequence having those initial values and recurrence.",
                DescribeRole.Definition),
            Node("sumWindow", "Actual linear windows", WindowFormula(false),
                "U is the sum of G(t+1) through G(t+k). Every natural shift t is retained, and the length-zero window is zero.",
                DescribeRole.Definition),
            Node("squareWindow", "Actual square windows", WindowFormula(true),
                "W sums the squares of exactly the same terms. It is an integer sum, with no restriction on the signs or common factors of the initial values.",
                DescribeRole.Definition),
            Node("sumGcd", "The normalized linear gcd", GcdFormula(false),
                "A is a natural gcd of the first two actual windows. The result proves that an arbitrary integer d divides A exactly when it divides U at every natural shift, so this finite expression represents the source's infinite gcd.",
                DescribeRole.Definition),
            Node("squareGcd", "The normalized square gcd", GcdFormula(true),
                "B is the nested natural gcd of the first three square windows. Its universal integer-divisor specification is proved for all shifts, including d=0. Absolute values only normalize the gcd; they do not restrict the source sequence.",
                DescribeRole.Definition),
            Node("result", "The whole odd-length question", ResultFormula(),
                "For every integer pair a,b, both odd subsequences have one common positive period P from j=0, corresponding to length k=1. The theorem includes the initial values, recurrence uniqueness, both infinite-shift divisor specifications, and scaling by every signed integer c. Thus nonprimitive seeds require no additional hypothesis. For (0,0), both gcds are identically zero under the normalized convention; this extension is separate from the source's relatively-prime seed convention. No least-period assertion or even-length periodicity assertion is made.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mbirika-spilker-gibonacci-odd-block-gcd-periodicity"),
                    ResolutionKind.Proved)),
            Paragraph(Text("To see why the finite gcds retain all shifts, U obeys an order-two recurrence in t, while W obeys W(t+3)=2W(t+2)+2W(t+1)-W(t). Divisibility therefore propagates from the first two or three windows, respectively. Direct telescoping gives U(t,k)=G(t+k+2)-G(t+2) and W(t,k)=G(t+k)G(t+k+1)-G(t)G(t+1).")),
            Paragraph(Text("Write mu=b^2-ab-a^2 and Q(x,y)=y^2-xy-x^2. The step reverses Q, so Q(G(n),G(n+1))=(-1)^n mu. At odd k, A and B both divide M=2|mu|. For the linear family this follows by applying Q to the endpoint differences. For the square family, W(2,k)-3W(1,k)+W(0,k)=2mu. The golden integer norm of (a,b) is -mu; its zero-norm characterization shows that mu=0 occurs exactly at the zero pair.")),
            Paragraph(Text("For a nonzero pair, M is positive. The existing complete-state return for step on (ZMod M)^2 supplies R=(M^2)!, a positive return time. Integer reduction commutes with every step. Consequently the two telescoping endpoints are unchanged modulo M after increasing k by 2R. Both old and new odd-length gcds divide M; their universal divisor specifications give divisibility in both directions. This yields the common odd-index period P=R. The factorial is a symbolic existence witness and is not asserted to be minimal.")),
            Paragraph(Text("Guyer-Mbirika, arXiv:2104.12262v2, Theorems 3.1 and 3.5, supplies the linear finite-gcd and scaling formulas. Mbirika-Spilker, arXiv:2204.12626v2, Theorems 3.4, 3.6 and 4.8, supplies the square finite formula, square scaling and odd fixed cap. Chen-Pan, Greatest Common Divisors of Shifted Horadam Sequences, JIS 23, Article 20.5.8, already proves the linear periodicity corollary and uses the finite modular-state method. With their parameters p=1,q=-1,s=-b,t=-(a+b),phi(j)=2j+2, their shifted pair is the linear gcd at length 2j+1. The joint conclusion here connects that method to the genuine infinite square-window gcd. Equivalent whole coverage in Spilker's 2016 generalized chapter remains unverified; the bounded source comparison does not establish first-publication priority."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Arith/FibonacciAtomic/GraftAffineClosure")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Norm"))]));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("odd-block-gcd-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula GFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var n = F.Id("n");
        return Disp(Seeds(All("n", Naturals(), EqOf(Call("G", a, b, n),
            Call("fst", Call("iterate", F.Id("step"), n, Seq(Open, a, Comma, Sp, b, Close)))))));
    }

    private static Formula WindowFormula(bool square)
    {
        var a = F.Id("a"); var b = F.Id("b"); var t = F.Id("t");
        var k = F.Id("k"); var i = F.Id("i");
        Formula term = Call("G", a, b, Add(Add(t, i), D(1)));
        if (square) term = Pow(term, D(2));
        return Disp(Seeds(All("t", Naturals(), All("k", Naturals(),
            EqOf(Call(square ? "W" : "U", a, b, t, k),
                Seq(Sum, Underscore, Grp(Seq(i, Sp, InMacro, Sp, Call("range", k))), Sp, term))))));
    }

    private static Formula GcdFormula(bool square)
    {
        var a = F.Id("a"); var b = F.Id("b"); var k = F.Id("k");
        string window = square ? "W" : "U";
        Formula rhs = Call("gcd", Abs(Call(window, a, b, D(0), k)),
            Abs(Call(window, a, b, D(1), k)));
        if (square) rhs = Call("gcd", rhs, Abs(Call("W", a, b, D(2), k)));
        return Disp(Seeds(All("k", Naturals(), EqOf(Call(square ? "B" : "A", a, b, k), rhs))));
    }

    private static Formula ResultFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var n = F.Id("n"); var u = F.Id("u"); var k = F.Id("k");
        var d = F.Id("d"); var t = F.Id("t"); var j = F.Id("j"); var p = F.Id("P");
        Formula G(Formula index) => Call("G", a, b, index);
        Formula U(Formula index) => Call("u", index);
        var initial = And(EqOf(G(D(0)), a), EqOf(G(D(1)), b),
            All("n", Naturals(), EqOf(G(Add(n, D(2))), Add(G(n), G(Add(n, D(1)))))));
        var unique = All("u", Seq(Naturals(), Sp, To, Sp, Integers()),
            Imp(EqOf(U(D(0)), a), Imp(EqOf(U(D(1)), b),
                Imp(All("n", Naturals(), EqOf(U(Add(n, D(2))), Add(U(n), U(Add(n, D(1)))))),
                    All("n", Naturals(), EqOf(U(n), G(n)))))));
        var specs = All("k", Naturals(), All("d", Integers(), And(
            IffOf(Div(d, Call("A", a, b, k)), All("t", Naturals(), Div(d, Call("U", a, b, t, k)))),
            IffOf(Div(d, Call("B", a, b, k)), All("t", Naturals(), Div(d, Call("W", a, b, t, k)))))));
        var scale = All("c", Integers(), All("k", Naturals(), And(
            EqOf(Call("A", Mul(c, a), Mul(c, b), k), Mul(Abs(c), Call("A", a, b, k))),
            EqOf(Call("B", Mul(c, a), Mul(c, b), k), Mul(Pow(Abs(c), D(2)), Call("B", a, b, k))))));
        var next = Add(Mul(D(2), Par(Add(j, p))), D(1));
        var now = Add(Mul(D(2), j), D(1));
        var period = Some("P", Naturals(), And(Less(D(0), p), All("j", Naturals(), And(
            EqOf(Call("A", a, b, next), Call("A", a, b, now)),
            EqOf(Call("B", a, b, next), Call("B", a, b, now))))));
        var zero = Imp(And(EqOf(a, D(0)), EqOf(b, D(0))), All("k", Naturals(), And(
            EqOf(Call("A", a, b, k), D(0)), EqOf(Call("B", a, b, k), D(0)))));
        return Disp(Seeds(And(initial, unique, specs, scale, period, zero)));
    }

    private static Formula Seeds(Formula body) => All("a", Integers(), All("b", Integers(), body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula EqOf(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Div(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Less(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula IffOf(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula And(params Formula[] terms)
    {
        Formula result = Par(terms[^1]);
        for (int i = terms.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Par(terms[i]), FormulaLogicOperator.And, result);
        return result;
    }
}
