using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.GeneratingFunctions;

internal sealed class KotesovecA265840Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265840.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kotesovec2018weighteddistinct");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithm of the weighted distinct-partition coefficient has Kotesovec's ratio asymptotic.",
        H("Kotesovec's logarithmic limit for A265840"),
        Blocks(
            Node("a", "The source coefficient", DefinitionBody(), true, true,
                "OEIS A265840, NAME (unpaginated): \"Expansion of Product_{k>=1} (1 + k^3*x^k).\" The coefficient index n ranges over all natural numbers, including zero. Only factors with index at most n contribute to degree n; the empty product gives a(0) = 1."),
            Node("claim", "The source asymptotic", Equal(V("claim"), Parenthesized(ClaimBody())), true, true,
                "OEIS A265840, FORMULA (unpaginated): \"Conjecture: log(a(n)) ~ 3*sqrt(n/2) * (log(2*n) - 2).\" The symbol ~ means that the real quotient tends to one along all natural indices. Real.log and real division are total at the finitely many indices where their usual positive-domain interpretation does not apply."),
            Node("result", "The proved logarithmic limit", ClaimBody(), false, false,
                "A distinct partition whose parts are almost the first M positive integers contributes at least the r-th power of M factorial, where M is the largest index with M(M+1)/2 at most n. Every individual partition has controlled product, and the logarithm of the number of distinct partitions is at most twice the square root of n. The resulting two-sided estimates differ from r times the square root of 2n times (the logarithm of that square root minus one) by at most a constant depending on r times the square root of n. Dividing by the displayed denominator proves the ratio limit. This does not identify an additive second term or a coefficient prefactor."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        bool definition, bool literature, string prose) => Describe.Lean(
            DescribeId.Create("kotesoveca265840-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula LogOf(Formula a) => App(Qualified("Real", "log"), a);
    private static Formula SqrtOf(Formula a) => App(Qualified("Real", "sqrt"), a);
    private static Formula Coefficient(Formula exponent, Formula n)
    {
        var k = V("k");
        var factor = Cast(Add(D(1), Mul(App(Qualified("Polynomial", "C"), Pow(k, exponent)),
            Pow(Qualified("Polynomial", "X"), k))), Call("Polynomial", NatType()));
        var product = Seq(new Formula.Subscript(F.Prod,
            Seq(k, Sp, InMacro, Sp, App(Qualified("Finset", "Icc"), D(1), n))), Sp, factor);
        return App(Qualified("Polynomial", "coeff"), Parenthesized(product), n);
    }
    private static Formula DefinitionBody() => All("n", NatType(),
        Equal(Call("a", V("n")), Coefficient(D(3), V("n"))));
    private static Formula Denominator(Formula n)
    {
        var nr = Cast(n, RealType());
        var root = SqrtOf(new Formula.Fraction(nr, D(2)));
        root = Mul(D(3), root);
        return Mul(root, Sub(LogOf(Mul(D(2), nr)), D(2)));
    }
    private static Formula RatioLimit(Formula numerator, Formula denominator) =>
        App(Qualified("Filter", "Tendsto"),
            Parenthesized(Seq(V("n"), Colon, Sp, NatType(), Sp, Mapsto, Sp,
                new Formula.Fraction(LogOf(Cast(numerator, RealType())), denominator))),
            Qualified("Filter", "atTop"), Call("nhds", Cast(D(1), RealType())));
    private static Formula ClaimBody() => RatioLimit(Call("a", V("n")), Denominator(V("n")));
}
