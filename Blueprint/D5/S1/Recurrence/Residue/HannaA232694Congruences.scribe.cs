using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA232694CongruencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaA232694Congruences.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create(
        "D5/L/RecurrenceComposition/hanna2013derivativesubstitutioncongruences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both nominated congruences hold for every factorial-normalized coefficient of OEIS A232694.",
        H("Hanna A232694: congruences of exponential coefficients"),
        Blocks(
            Node("IsSolution", "The rational formal-series equation", SolutionDefinition(),
                "%N A232694 E.g.f. A(x) satisfies: A'(x) = A(x*A'(x)^4) with A(0)=1. %C A232694  CONJECTURES. %C A232694 a(n) == 0 (mod 3) for n>=3. %C A232694 a(n) == 1 (mod 8) for n>=0. %e A232694 E.g.f.: A(x) = 1 + x + x^2/2! + 9*x^3/3! + 177*x^4/4! + 5601*x^5/5! +... OEIS A232694 has no page number; these are its NAME, COMMENTS and EXAMPLE lines. All indices are natural numbers, starting at zero. The displayed factorials define the exponential coefficients. The formal derivative and substitution act in PowerSeries Rat; no analytic convergence is assumed.",
                AssessedProvenance.FromLiterature(Source()), DescribeRole.Definition),
            Node("claim", "The two congruences", Equal(V("claim"), ClaimBody()),
                "%N A232694 E.g.f. A(x) satisfies: A'(x) = A(x*A'(x)^4) with A(0)=1. %C A232694  CONJECTURES. %C A232694 a(n) == 0 (mod 3) for n>=3. %C A232694 a(n) == 1 (mod 8) for n>=0. %e A232694 E.g.f.: A(x) = 1 + x + x^2/2! + 9*x^3/3! + 177*x^4/4! + 5601*x^5/5! +... The equation is encoded by IsSolution. The integer sequence a is required to have eCoeff(A,n)=(a(n):Rat) at every index, so integrality is part of the conclusion. Divisibility expresses precisely the two nominated residue assertions. Other COMMENTS assertions, when present, are outside this proposition.",
                AssessedProvenance.FromLiterature(Source()), DescribeRole.Definition),
            Node("result", "The congruences hold at every index", ClaimBody(),
                "An integral triangular recurrence transfers the residues of an approximate solution to every exact solution. "
                + "The finite polynomial residual has divisible exponential coefficients in every degree. "
                + "The exponential approximate solution supplies the constant residue where used.",
                AssessedProvenance.FromRepo(Source()), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hefg-a232694"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hanna-a232694-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            resolution);

    private static Formula SolutionDefinition()
    {
        var a = V("A");
        return All("A", PS(), Iff(Call("IsSolution", a), And(
            Equal(Call("constantCoeff", a), Num(1)), Equal(Der(a), App(Qualified("PowerSeries", "subst"), a, Multiply(V("X"), Pow(Der(a), Num(4))))))));
    }

    private static Formula ClaimBody()
    {
        var a = V("A"); var n = V("n");
        return All("A", PS(), Imp(Call("IsSolution", a), Ex("a", Arr(N(), Z()),
            And(All("n", N(), Equal(Coeff(a, n), Cast(App(V("a"), n), Q()))),
                And(All("n", N(), Imp(Leq(Num(3), n), Dvd(Cast(Num(3), Z()), App(V("a"), n)))), All("n", N(), Dvd(Cast(Num(8), Z()), Subtract(App(V("a"), n), Num(1)))))))));
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
    private static Formula Pow(Formula f, Formula n) => new Formula.Power(f, n);
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
