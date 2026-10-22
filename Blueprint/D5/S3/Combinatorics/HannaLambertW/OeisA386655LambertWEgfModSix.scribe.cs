using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.HannaLambertW;

internal sealed class OeisA386655LambertWEgfModSix_Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a386655a386658");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrality and a period-six congruence for Hanna's Lambert W exponential coefficients.",
        H("Hanna's OEIS 386655 congruence"), Blocks(
            Node("W", "The Lambert W series", WFormula(), "The coefficient of positive degree m is (-m)^(m-1)/m!, and the constant coefficient is zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("egf", "The exponential generating coefficient", EgfFormula(), "For q=2 the entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!. The series in the n-th summand has order at least n; therefore only n at most m contributes to coefficient m. The casts and divisions are in the rational field.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "OEIS A386655", Disp(Seq(Bind("m", Nat()), Eqn(Call("a", F.Id("m")), Call("egf", D(2), F.Id("m"))))), "The entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!. Here egf is the rational coefficient function of OeisA386655LambertWEgfModSix.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed six-term pattern", Disp(Eqn(Named("claim"), Parenthesized(ClaimBody()))), "Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating. This is the COMMENTS sentence of OEIS A386655 (unpaginated). The integer z has rational cast a(n); getD uses the zero-based index (n-6) mod 6 and default zero. Both remainder operations and natural subtraction are Lean integer or natural operations, respectively.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("closedZ", "An integral closed form", ClosedFormula(), "The FORMULA field of OEIS A386655 (unpaginated) reads verbatim: a(n) = Sum_{k=0..n} binomial(n,k) * 2^(k*(k+1)) * (2^k - (n-k))^(n-k-1). Replace 2 by the natural parameter q. Separate the last summand, whose exponent in the source formula is negative, as q^(n*n). Every remaining exponent is a natural number. Subtractions in exponents and in n-k are natural subtraction, followed by the displayed integer cast.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("egf_closed", "Integrality for every q and n", ClosedIdentity(), "Lagrange inversion evaluates the coefficients of exp(y W). Binomial expansion and triangular reindexing then give the integral finite sum. This identity also supplies the integer z for each of the four coefficient sequences.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("closedZ_reduce", "Period six after the sixth index", ReductionFormula(), "In ZMod(6), x cubed equals x. The binomial transform satisfies B(n+9)=B(n+3), and its endpoint corrections depend only on n modulo six. Casting the resulting identity back to integer remainders gives the displayed formula for every q.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Hanna's congruence", Disp(ClaimBody()), "The integral closed form and its six-term periodicity reduce the assertion to the six indices from six through eleven, which give the displayed pattern.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a386655-hanna-lambert-w-egf-mod-six"), ResolutionKind.Proved)))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a386655-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Bind(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Pattern() => Seq(OpenBracket, D(1), Comma, Sp, D(0), Comma, Sp, D(3), Comma, Sp, D(0), Comma, Sp, D(3), Comma, Sp, D(2), CloseBracket);
    private static Formula ClaimBody() => Seq(Bind("n", Nat()), Impl(Seq(D(6), Sp, Le, Sp, F.Id("n")),
        Seq(Exists, Sp, F.Id("z"), Colon, Sp, Z(), Comma, Sp,
            And(Eqn(Cast(F.Id("z"), Rat()), Call("a", F.Id("n"))),
                Eqn(Mod(F.Id("z"), D(6)), Call("getD", Pattern(),
                    Mod(Parenthesized(Sub(F.Id("n"), D(6))), D(6)), D(0)))))));

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Fact(Formula a) => Seq(a, Bang);
    private static Formula Sum(string name, Formula upper, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(name), Sp, InMacro, Sp, Call("range", upper))), Sp, Parenthesized(body));
    private static Formula WFormula() => Disp(Eqn(Named("W"), Call("mk", Parenthesized(Seq(
        F.Id("m"), Colon, Sp, Nat(), Sp, Mapsto, Sp, Named("if"), Sp,
        Parenthesized(Eqn(F.Id("m"), D(0))), Sp, Named("then"), Sp, D(0), Sp,
        Named("else"), Sp, new Formula.Fraction(
            Pow(Seq(Minus, Cast(F.Id("m"), Rat())), Sub(F.Id("m"), D(1))),
            Cast(Fact(F.Id("m")), Rat())))))));
    private static Formula EgfFormula()
    {
        var m = F.Id("m"); var n = F.Id("n"); var q = F.Id("q");
        return Disp(Seq(Bind("q", Nat()), Bind("m", Nat()), Eqn(Call("egf", q, m),
            Mul(Cast(Fact(m), Rat()), Sum("n", Add(m, D(1)), new Formula.Fraction(
                Call("coeff", m, Pow(Add(Mul(Call("C", Pow(Cast(q, Rat()), n)), F.Id("X")), Named("W")), n)),
                Cast(Fact(n), Rat())))))));
    }
    private static Formula ClosedFormula()
    {
        var q = F.Id("q"); var n = F.Id("n"); var k = F.Id("k");
        return Disp(Seq(Bind("q", Nat()), Bind("n", Nat()), Eqn(Call("closedZ", q, n),
            Add(Pow(Cast(q, Z()), Mul(n, n)), Sum("k", n,
                Mul(Mul(Cast(Call("choose", n, k), Z()), Pow(Cast(q, Z()), Mul(k, Add(k, D(1))))),
                    Pow(Sub(Pow(Cast(q, Z()), k), Cast(Sub(n, k), Z())), Sub(Sub(n, k), D(1)))))))));
    }
    private static Formula ClosedIdentity() => Disp(Seq(Bind("q", Nat()), Bind("n", Nat()),
        Eqn(Call("egf", F.Id("q"), F.Id("n")), Cast(Call("closedZ", F.Id("q"), F.Id("n")), Rat()))));
    private static Formula ReductionFormula() => Disp(Seq(Bind("q", Nat()), Bind("n", Nat()),
        Impl(Seq(D(6), Sp, Le, Sp, F.Id("n")), Eqn(Mod(Call("closedZ", F.Id("q"), F.Id("n")), D(6)),
            Mod(Call("closedZ", F.Id("q"), Add(Mod(Parenthesized(Sub(F.Id("n"), D(6))), D(6)), D(6))), D(6))))));

}
