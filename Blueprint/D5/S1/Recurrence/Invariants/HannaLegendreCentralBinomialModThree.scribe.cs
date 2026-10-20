using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaLegendreCentralBinomialModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2014a246056a246423");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's binomial-square generating function has the asserted residues at every coefficient.",
        H("Hanna's ternary-digit residue theorem"),
        Blocks(
            Node("term", "The rational summand", TermFormula(2),
                "OEIS A246056, unpaginated Name: \"G.f.: Sum_{n>=0} x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k].\" The variable is the formal power-series variable and both sums include indices zero through n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The generating function", AFormula(),
                "OEIS A246056, unpaginated Name: \"G.f.: Sum_{n>=0} x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k].\" Its coefficient at m uses n from zero through m, because term n has order at least n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The residue conjecture", IffBody(X("claim"), ClaimBody()),
                "OEIS A246056, unpaginated Comments: \"Conjecture: a(n) == 1 (mod 3) when n = 2*A005836(k) for k >= 0, and a(n) == 0 (mod 3) otherwise, where A005836 gives numbers whose base-3 representation contains no 2.\" The letter n ranges over all natural indices and z is the integer equal to the rational coefficient. Zero has an empty digit list and is included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", ClaimBody(),
                "The integer lift allows coefficientwise reduction. The alternating binomial-square transform and Lucas recurrence identify the ternary support and its signed residue.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a246056-a246423-legendre-central-binomial"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula power) =>
        new Formula.Power(Parenthesized(value), power);
    private static Formula Mul(params Formula[] values) =>
        values.Aggregate((a, b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, type, Comma, Sp, body);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, type));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Choose(Formula n, Formula k) => App(Qualified("Nat", "choose"), n, k);
    private static Formula Coeff(Formula n, Formula series) => App(Qualified("PowerSeries", "coeff"), n, series);
    private static Formula Constant(Formula value) => App(Qualified("PowerSeries", "C"), value);
    private static Formula PSeries(Formula type) => Call("PowerSeries", type);
    private static Formula Var() => Qualified("PowerSeries", "X");
    private static Formula SumRange(string name, Formula bound, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(X(name), InMacro, Sp, App(Qualified("Finset", "range"), bound))), body);
    private static Formula LambdaBody(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(X("fun")), Sp, Parenthesized(Seq(X(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Mk(Formula body) => App(Qualified("PowerSeries", "mk"), body);



    private static Formula PolynomialBody(byte a) => SumRange("k", Add(X("n"), D(1)),
        Mul(Constant(Mul(Pow(Cast(Choose(X("n"), X("k")), Rat()), D(2)), Pow(D(a), X("k")))), Pow(Var(), X("k"))));
    private static Formula TermBody(byte c) => Mul(Pow(Var(), X("n")),
        Pow(Pow(Sub(D(1), Mul(D(c), Var())), Add(Mul(D(2), X("n")), D(1))), Seq(Minus, D(1))),
        Parenthesized(PolynomialBody(2)), Parenthesized(PolynomialBody(3)));
    private static Formula TermFormula(byte c) => All("n", N(),
        Eqn(Call("term", X("n")), Cast(TermBody(c), PSeries(Rat()))));
    private static Formula AFormula() => Eqn(X("A"), Mk(LambdaBody("m", N(),
        Coeff(X("m"), SumRange("n", Add(X("m"), D(1)), Call("term", X("n")))))));
    private static Formula Congruent(byte residue, byte modulus) =>
        Seq(X("z"), Sp, Equiv, Sp, D(residue), Sp, Pmod, Grp(D(modulus)));
    private static Formula ExistsBody(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, X(name), Colon, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesBody(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffBody(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula NotBody(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Support() => ExistsBody("m", N(), And(
        Eqn(X("n"), Mul(D(2), X("m"))), NotBody(Seq(D(2), InMacro, Sp, App(Qualified("Nat", "digits"), D(3), X("m"))))));
    private static Formula ClaimBody() => All("n", N(), ExistsBody("z", Z(), And(
        Eqn(Coeff(X("n"), X("A")), Cast(X("z"), Rat())), And(
            ImpliesBody(Support(), Congruent(1, 3)), ImpliesBody(NotBody(Support()), Congruent(0, 3))))));
}
