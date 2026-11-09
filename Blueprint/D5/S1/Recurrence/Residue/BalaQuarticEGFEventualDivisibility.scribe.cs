using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class BalaQuarticEGFEventualDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/BalaQuarticEGFEventualDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2017a281428bala2026");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive modulus coprime to six eventually divides the A281428 coefficients.",
        H("Bala's A281428 Eventual Divisibility Conjecture"),
        Blocks(
            Paragraph(Text("All series are rational formal power series. The integral has constant "
                + "coefficient zero. The exponentials below are substitutions into PowerSeries.exp. "
                + "For the sequence in the OEIS example, a(n)=(2n)! times coeff(2n,C); odd degrees "
                + "are omitted. All indices and moduli are natural numbers. Equality to N times "
                + "an integer expresses integer divisibility.")),
            Node("IsSourceSeries", "The source equation", All("C", PS(), IffFormula(
                Call("IsSourceSeries", V("C")), SourceBody(V("C")))),
                "OEIS A281428, revision 49, NAME (no page number): "
                + "\"E.g.f. C(x) satisfies C(x) = cosh( Integral C(x)^4 dx ).\" "
                + "The EXAMPLE starts with 1 + x^2/2! + 17*x^4/4!, so C has constant coefficient one. "
                + "The displayed equation writes cosh as the half-sum of two exponential substitutions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Bala's first conjecture", IffFormula(V("claim"), ClaimBody()),
                "OEIS A281428, revision 49, COMMENTS, Peter Bala, item 1 (no page number): "
                + "\"1) If N is not divisble by either 2 or 3 then there exists n_0 such that N divides a(n) for all n >= n_0.\" "
                + "The EXAMPLE uses even-degree factorial normalization. The existence conjunct "
                + "asserts that the original normalized series equation has a solution.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Eventual divisibility for every coprime modulus", ClaimBody(),
                "The differential system gives integer factorial-normalized coefficients. With S the "
                + "corresponding hyperbolic sine and u=S/C, one obtains u-u^3/3=X and (1-u^2)C^2=1. "
                + "Degree induction places the ordinary coefficients in every rational subring containing "
                + "1/2 and 1/3. Their reduced denominators are therefore coprime to N. For "
                + "n at least (N+1)/2, with natural division, N divides (2n)!, and integer Euclid "
                + "cancellation proves the assertion. This sufficient onset is not asserted minimal.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala281428"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala281428-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(left, Sp, Iff, Sp, Parenthesized(right));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Negate(Formula value) => new Formula.Negate(value);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula ExpSubst(Formula value) => Qualified("PowerSeries", "subst", value,
        Qualified("PowerSeries", "exp", Q()));
    private static Formula SourceBody(Formula c)
    {
        var input = IntegralFormula(Pow(c, D(4)));
        return And(Equal(Qualified("PowerSeries", "constantCoeff", c), D(1)),
            Equal(c, Multiply(Qualified("PowerSeries", "C", new Formula.Fraction(D(1), D(2))),
                Parenthesized(Add(ExpSubst(input), ExpSubst(Negate(input)))))));
    }
    private static Formula IntegralFormula(Formula f)
    {
        var k = V("k");
        var body = Seq(Seq(V("match"), Sp, V("j")), Sp, V("with"), Sp,
            Mid, Sp, D(0), Sp, Mapsto, Sp, D(0), Sp,
            Mid, Sp, Add(k, D(1)), Sp, Mapsto, Sp,
            new Formula.Fraction(Qualified("PowerSeries", "coeff", k, f), Cast(Add(k, D(1)), Q())));
        var lambda = Parenthesized(Seq(V("fun"), Sp, V("j"), Colon, Sp, N(), Sp, Mapsto, Sp, body));
        return Qualified("PowerSeries", "mk", lambda);
    }
    private static Formula ClaimBody()
    {
        var c = V("C"); var n = V("n"); var modulus = V("N");
        var twice = Multiply(D(2), n);
        var coefficient = Multiply(Cast(Qualified("Nat", "factorial", twice), Q()),
            Qualified("PowerSeries", "coeff", twice, c));
        var eventual = Ex("n0", N(), All("n", N(), Imp(
            new Formula.Relation(V("n0"), FormulaRelationOperator.LessThanOrEqual, n),
            Ex("k", Z(), Equal(coefficient, Multiply(Cast(modulus, Q()), Cast(V("k"), Q())))))));
        return And(Ex("C", PS(), Call("IsSourceSeries", c)),
            All("C", PS(), Imp(Call("IsSourceSeries", c), All("N", N(), Imp(
                new Formula.Relation(D(0), FormulaRelationOperator.LessThan, modulus), Imp(
                    Qualified("Nat", "Coprime", modulus, D(6)), eventual))))));
    }
}
