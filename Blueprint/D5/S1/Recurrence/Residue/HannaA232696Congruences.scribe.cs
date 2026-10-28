using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA232696CongruencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaA232696Congruences.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create(
        "D5/L/RecurrenceComposition/hanna2013derivativesubstitutioncongruences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both nominated congruences hold for every factorial-normalized coefficient of OEIS A232696.",
        H("Hanna A232696: congruences of exponential coefficients"),
        Blocks(
            Node("IsSolution", "The rational formal-series equation", SolutionDefinition(),
                "%N A232696 E.g.f. A(x) satisfies: A'(x) = A(x/A'(x)) with A(0)=1. %C A232696  CONJECTURES. %C A232696 a(n) == 0 (mod 2) for n>=4. %C A232696 a(n) == 0 (mod 2^2) for n>=10. %C A232696 a(n) == 0 (mod 2^3) for n>=18. %C A232696 a(n) == 0 (mod 2^k) for n>=(8*n-6) for k>1. %e A232696 E.g.f.: A(x) = 1 + x + x^2/2! - x^3/3! + 2*x^4/4! + 6*x^5/5! - 264*x^6/6! + 5370*x^7/7! +... OEIS A232696 has no page number; these are its NAME, COMMENTS and EXAMPLE lines. All indices are natural numbers, starting at zero. The displayed factorials define the exponential coefficients. The formal derivative and substitution act in PowerSeries Rat; no analytic convergence is assumed.",
                AssessedProvenance.FromLiterature(Source()), DescribeRole.Definition),
            Node("claim", "The two congruences", Equal(V("claim"), ClaimBody()),
                "%N A232696 E.g.f. A(x) satisfies: A'(x) = A(x/A'(x)) with A(0)=1. %C A232696  CONJECTURES. %C A232696 a(n) == 0 (mod 2) for n>=4. %C A232696 a(n) == 0 (mod 2^2) for n>=10. %C A232696 a(n) == 0 (mod 2^3) for n>=18. %C A232696 a(n) == 0 (mod 2^k) for n>=(8*n-6) for k>1. %e A232696 E.g.f.: A(x) = 1 + x + x^2/2! - x^3/3! + 2*x^4/4! + 6*x^5/5! - 264*x^6/6! + 5370*x^7/7! +... The equation is encoded by IsSolution. The integer sequence a is required to have eCoeff(A,n)=(a(n):Rat) at every index, so integrality is part of the conclusion. Divisibility expresses precisely the two nominated residue assertions. Other COMMENTS assertions, when present, are outside this proposition.",
                AssessedProvenance.FromLiterature(Source()), DescribeRole.Definition),
            Node("result", "The congruences hold at every index", ClaimBody(),
                "An integral triangular recurrence transfers the residues of an approximate solution to every exact solution. "
                + "Multiplication by the third or ninth power of the approximate derivative makes the residual polynomial. "
                + "Its exponential coefficients are divisible by two or four, respectively. "
                + "Cancellation of the integral series with constant coefficient one gives the two divisibility tails.",
                AssessedProvenance.FromRepo(Source()), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hefg-egfcongruences"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hanna-a232696-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            resolution);

    private static Formula SolutionDefinition()
    {
        var a = V("A");
        return All("A", PS(), Iff(Call("IsSolution", a), And(
            Equal(Call("constantCoeff", a), Num(1)), Equal(Der(a), App(Qualified("PowerSeries", "subst"), a, Multiply(V("X"), App(Qualified("Inv", "inv"), Der(a))))))));
    }

    private static Formula ClaimBody()
    {
        var a = V("A"); var n = V("n");
        return All("A", PS(), Imp(Call("IsSolution", a), Ex("a", Arr(N(), Z()),
            And(All("n", N(), Equal(Coeff(a, n), Cast(App(V("a"), n), Q()))),
                And(All("n", N(), Imp(Leq(Num(4), n), Dvd(Cast(Num(2), Z()), App(V("a"), n)))), All("n", N(), Imp(Leq(Num(10), n), Dvd(Cast(Num(4), Z()), App(V("a"), n)))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Der(Formula a) => App(Qualified("PowerSeries", "derivative"), a);
    private static Formula Coeff(Formula a, Formula n) => Call("eCoeff", a, n);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
}
