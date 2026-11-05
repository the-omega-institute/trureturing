using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TebniA355257DivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/TebniA355257Divisibility.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/luschnytebni2022a355257");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The divisibility criterion and shared prime residues of the logarithmic coefficient array.",
        H("Tebni's logarithmic coefficient divisibility criterion"),
        Blocks(
            Paragraph(Text("PowerSeries.logOf is the formal logarithm at a series with constant coefficient one. "
                + "All indices are natural numbers starting at zero. In T, Nat.div is natural-number division, "
                + "followed by the displayed cast to integers. Int.ModEq takes the integer modulus first. "
                + "The inverse series invOneSubPow includes exponent zero.")),
            Node("L", "The logarithmic series", LFormula(),
                "OEIS A355257, revision 37, NAME (unpaginated): "
                + "\"Array read by ascending antidiagonals. A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n, for 0 <= k <= n.\" "
                + "L is the formal logarithm of the numerator times the inverse denominator over Q.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The source coefficient array", AFormula(),
                "OEIS A355257, revision 37, NAME (unpaginated): "
                + "\"Array read by ascending antidiagonals. A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n, for 0 <= k <= n.\" "
                + "The same formal coefficient expression defines A for every natural n and k, including n=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T", "Integer summands", TFormula(),
                "Each summand multiplies the integer factorial quotient by 2^j-1 and by the degree k-j coefficient "
                + "of the integral inverse power of 1-X. The j=0 term vanishes.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("Z", "The representing integer", ZFormula(),
                "The finite sum includes j=0 through j=k. It represents the rational coefficient A(n,k) as an integer.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("A_eq_Z", "Integrality of every coefficient", All("n", N(), All("k", N(),
                Eq(Call("A", V("n"), V("k")), Cast(Call("Z", V("n"), V("k")), QType())))),
                "The logarithmic degree-j coefficient is (2^j-1)/j. Coefficient convolution with the inverse "
                + "power series and factorial divisibility give the displayed integer sum, also when n=0 or k=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("prime_residue", "Prime residues", PrimeFormula(),
                "All summands with j<p vanish modulo p. Wilson's theorem and the finite-field power identity "
                + "make the remaining summand equal to minus one. This residue also determines the prime quotient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("even_pred_divides", "The divisor preceding a prime", PredFormula(),
                "Modulo p-1 only the j=p-1 summand can remain. For primes at least seven, p-1 divides (p-2)!. "
                + "At p=3 and p=5 the even factor n supplies the missing divisibility; p=2 has modulus one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The source conjecture", Eq(V("claim"), Parenthesized(ClaimBody())),
                "OEIS A355257, revision 37, COMMENTS (unpaginated): "
                + "\"Conjecture: Let n >= 0, k >= 1 and k != 4. Then k divides A(n, k) if and only if k is not prime.\" "
                + "An integer z equal to A(n,k) expresses integer divisibility of the rational coefficient. "
                + "The natural index n includes zero, and k is positive and different from four.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The divisibility criterion holds", ClaimBody(),
                "Modulo k all terms below j=k vanish. The remaining value is (k-1)! times 2^k-1. "
                + "For prime k it is minus one; for composite k other than four the factorial is divisible by k. "
                + "The index k=1 is included.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("tebni355257-logcoef"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("tebni355257-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula LFormula()
    {
        var x = V("X");
        return Eq(V("L"), Qualified("PowerSeries", "logOf", Mul(Parenthesized(Sub(D(1), x)),
            Pow(Parenthesized(Sub(D(1), Mul(D(2), x))), Seq(Minus, D(1))))));
    }

    private static Formula AFormula()
    {
        var n = V("n"); var k = V("k");
        var inverse = Pow(Parenthesized(Pow(Parenthesized(Sub(D(1), V("X"))), n)), Seq(Minus, D(1)));
        return All("n", N(), All("k", N(), Eq(Call("A", n, k),
            Mul(Cast(Fact(k), QType()), Qualified("PowerSeries", "coeff", k, Mul(V("L"), inverse))))));
    }

    private static Formula TFormula()
    {
        var n = V("n"); var k = V("k"); var j = V("j");
        var quotient = Qualified("Nat", "div", Fact(k), j);
        var series = Call("val", Qualified("PowerSeries", "invOneSubPow", ZType(), n));
        return All("n", N(), All("k", N(), All("j", N(), Eq(Call("T", n, k, j),
            Mul(Mul(Cast(quotient, ZType()), Parenthesized(Sub(Pow(Cast(D(2), ZType()), j), D(1)))),
                Qualified("PowerSeries", "coeff", Sub(k, j), series))))));
    }

    private static Formula ZFormula()
    {
        var n = V("n"); var k = V("k"); var j = V("j");
        var range = Qualified("Finset", "range", Add(k, D(1)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, range)), Sp, Call("T", n, k, j));
        return All("n", N(), All("k", N(), Eq(Call("Z", n, k), sum)));
    }

    private static Formula PrimeFormula() => All("n", N(), All("p", N(),
        Imp(Qualified("Nat", "Prime", V("p")), Qualified("Int", "ModEq", Cast(V("p"), ZType()),
            Call("Z", V("n"), V("p")), Seq(Minus, D(1))))));

    private static Formula PredFormula() => All("n", N(), All("p", N(),
        Imp(Qualified("Nat", "Prime", V("p")), Imp(Call("Even", V("n")),
            Dvd(Parenthesized(Sub(Cast(V("p"), ZType()), D(1))), Call("Z", V("n"), V("p")))))));

    private static Formula ClaimBody()
    {
        var n = V("n"); var k = V("k"); var z = V("z");
        return All("n", N(), All("k", N(), Imp(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, k),
            Imp(new Formula.Relation(k, FormulaRelationOperator.NotEqual, D(4)), Ex("z", ZType(),
                And(Eq(Cast(z, QType()), Call("A", n, k)),
                    new Formula.Logic(Parenthesized(Dvd(Cast(k, ZType()), z)), FormulaLogicOperator.Iff,
                        new Formula.Not(Qualified("Nat", "Prime", k)))))))));
    }

    private static Formula Fact(Formula value) => Seq(value, Bang);
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Named(owner), Dot, Named(name)), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula ZType() => Seq(Mathbb, Grp(V("Z")));
    private static Formula QType() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
}
