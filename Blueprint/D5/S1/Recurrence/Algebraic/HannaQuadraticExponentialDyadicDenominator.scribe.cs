using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaQuadraticExponentialDyadicDenominatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaQuadraticExponentialDyadicDenominator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2010a174491");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact reduced denominators of Hanna's quadratic-exponent formal exponential.",
        H("Hanna's Quadratic Exponential Has Exact Dyadic Denominators"),
        Blocks(
            Node("logarithmInput", "The logarithmic input", InputFormula(),
                "OEIS A174491, unpaginated %N: Denominator in the coefficient of x^n in exp( Sum_{m>=1} x^m/(m*2^(m^2)) ). "
                    + "The rational formal series inside the exponential has zero constant coefficient and coefficient 1/(m*2^(m^2)) at positive m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSeries", "The source series equation",
                All("F", PS(), Seq(Call("IsSourceSeries", V("F")), Sp, Iff, Sp,
                    Parenthesized(Eqn(V("F"), Exponential())))),
                "OEIS A174491, unpaginated %N: Denominator in the coefficient of x^n in exp( Sum_{m>=1} x^m/(m*2^(m^2)) ). "
                    + "F is a rational formal power series equal to the formal exponential of logarithmInput.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's denominator conjecture",
                Seq(V("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody())),
                "OEIS A174491, unpaginated %F: a(n) = 2^(n^2)*A006519(n) where A006519(n) = highest power of 2 dividing n [conjecture]. "
                    + "Here Rat.den is the positive reduced denominator and padicValNat 2 n is the exponent of two in positive n. "
                    + "A006519 starts at one; the constant term and its denominator are each stated separately as one. "
                    + "The statement includes existence and quantifies over every rational formal series satisfying the displayed equation.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Exact reduced denominator at every positive index", ClaimBody(),
                "Differentiation gives a coefficient recurrence whose term with index zero has uniquely least two-adic valuation. "
                    + "For every odd prime, Fermat's identity and lifting the exponent make the logarithmic difference locally integral; "
                    + "the Dieudonne-Dwork criterion then excludes that prime from each reduced denominator. "
                    + "Prime valuations determine the denominator exactly. The same denominator assertion occurs in A174490.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaquadraticdyadic-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Exponential() => Qualified("PowerSeries", "subst", V("logarithmInput"),
        Qualified("PowerSeries", "exp", Q()));
    private static Formula Coeff(Formula index, Formula series) => Qualified("PowerSeries", "coeff", index, series);
    private static Formula Den(Formula value) => Qualified("Rat", "den", value);

    private static Formula InputFormula()
    {
        var m = V("m");
        var cast = Parenthesized(Seq(m, Colon, Sp, Q()));
        var coefficient = Seq(V("if"), Sp, Eqn(m, D(0)), Sp, V("then"), Sp, D(0), Sp,
            V("else"), Sp, new Formula.Fraction(D(1), Mul(cast, Pow(Parenthesized(Seq(D(2), Colon, Sp, Q())), Pow(m, D(2))))));
        var function = Parenthesized(Seq(V("fun"), Sp, m, Colon, Sp, N(), Sp, Mapsto, Sp, coefficient));
        return Eqn(V("logarithmInput"), Qualified("PowerSeries", "mk", function));
    }

    private static Formula ClaimBody()
    {
        var f = V("F"); var n = V("n");
        var positive = Seq(D(1), Sp, Leq, Sp, n);
        var denominator = Eqn(Den(Coeff(n, f)), Pow(D(2), Add(Pow(n, D(2)), Call("padicValNat", D(2), n))));
        var properties = And(Eqn(Coeff(D(0), f), D(1)),
            And(Eqn(Den(Coeff(D(0), f)), D(1)), All("n", N(), Imp(positive, denominator))));
        return And(Ex("F", PS(), Call("IsSourceSeries", f)),
            All("F", PS(), Imp(Call("IsSourceSeries", f), properties)));
    }
}
