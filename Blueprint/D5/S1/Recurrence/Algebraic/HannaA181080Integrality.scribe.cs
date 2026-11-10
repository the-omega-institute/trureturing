using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA181080IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA181080Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2010a181070family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients of Hanna's OEIS A181080 formal exponential.",
        H("Hanna A181080 Integrality"), Blocks(
            Node("logarithm", "The rational logarithm", Eqn(Call("logarithm"), Qualified("PowerSeries", "mk", Lam("m", N(), DiagonalSum(true, Pow(Cast(Choose(V("n"), V("k")), Q()), Add(Sub(V("n"), V("k")), D(1))))))),
                "OEIS A181080, NAME (web entry, no page number): \"Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k+1) * x^k] * x^n/n ).\" The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The formal exponential", Eqn(Call("A"), ExpOf(Call("logarithm"))),
                "OEIS A181080, NAME (web entry, no page number): \"Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k+1) * x^k] * x^n/n ).\" The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Integer coefficients", Iffn(Call("claim"), ClaimBody()),
                "OEIS A181080, first COMMENTS line (web entry, no page number): \"Conjecture: this sequence consists entirely of integers.\" The degree m ranges over all natural numbers, including zero; the integer z may depend on m.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality in every degree", ClaimBody(),
                "Every coefficient of the displayed formal exponential is an integer. The prime-scaling congruence and diagonal identity reduce the assertion to the Dold exponential integrality criterion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna181080"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannaa181080-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula a) => Qualified("PowerSeries", "coeff", n, a);
    private static Formula Choose(Formula n, Formula k) => Qualified("Nat", "choose", n, k);
    private static Formula ExpOf(Formula f) => Qualified("PowerSeries", "subst", f, Qualified("PowerSeries", "exp", Q()));
    private static Formula RangeSum(string index, Formula bound, Formula body) =>
        Qualified("Finset", "sum", Qualified("Finset", "range", bound), Lam(index, N(), body));
    private static Formula DiagonalSum(bool bounded, Formula value)
    {
        var n = V("n"); var k = V("k"); var m = V("m");
        var condition = And(Lt(D(0), n), Eqn(Add(n, k), m));
        var summand = Seq(V("if"), Sp, Parenthesized(condition), Sp, V("then"), Sp,
            new Formula.Fraction(value, Cast(n, Q())), Sp, V("else"), Sp, D(0));
        return RangeSum("n", Add(m, D(1)), RangeSum("k", Add(bounded ? n : m, D(1)), summand));
    }
    private static Formula ClaimBody() => All("m", N(), Ex("z", Z(), Eqn(Coeff(V("m"), Call("A")), Cast(V("z"), Q()))));
}
