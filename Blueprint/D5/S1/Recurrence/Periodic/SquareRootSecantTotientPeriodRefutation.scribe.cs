using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class SquareRootSecantTotientPeriodRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/bala2026a126156");
    private const string SourceName =
        "Expansion of e.g.f. sqrt(sec(sqrt(2)*x)), showing coefficients of only the even powers of x.";
    private const string SourceConjecture =
        "Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k), where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Mar 01 2026";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square-root secant sequence has no eventual period dividing the totient at modulus four.",
        H("A126156 and the Totient Period Bound"),
        Blocks(
            Paragraph(Text("The source is OEIS A126156, revision 110, NAME and the third COMMENTS entry; "
                + "the entry has no page numbers. The even coefficient at index n is scaled by (2n)!. "
                + "A rational power series A represents the positive square root through constant "
                + "coefficient one and A squared times cosSqrtTwo equal to one.")),
            Paragraph(Text("All sequence indices, moduli, onsets and periods are natural numbers. "
                + "An integer z expresses divisibility in the rational coefficient field. "
                + "Nat.div is natural-number division; the fraction in cosSqrtTwo is rational "
                + "division. The type annotations in parentheses show the casts to the rationals.")),
            Node("cosSqrtTwo", "The rational cosine series", CosineFormula(),
                "The coefficient at an even j is (-2) raised to j divided by two, divided by j factorial; "
                + "the coefficient at an odd j is zero. This is cos(sqrt(2)*x) over the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceEGF", "The square-root secant equation", SourceFormula(),
                SourceName + " (OEIS A126156, revision 110, NAME; no page number.) "
                + "The series has constant coefficient one and its square multiplied by cosSqrtTwo "
                + "is one. These equations select the formal square root with positive constant term.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Bala's eventual period assertion",
                Disp(Equality(V("claim"), Parenthesized(ClaimBody()))),
                SourceConjecture + " (OEIS A126156, revision 110, third COMMENTS entry; no page number.) "
                + "The expression (2n)! times PowerSeries.coeff(2n,A) is the zero-based sequence a(n). "
                + "The assertion includes existence of such an A and quantifies over every such A, "
                + "every positive modulus k, an eventual onset N and a positive period p dividing Nat.totient(k).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The totient period assertion is false",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "For each series satisfying the square-root secant equation, the scaled even "
                + "coefficients are integers and odd, and their two-step differences equal four "
                + "times an integer plus two. Integer derivative polynomials give the two-step "
                + "identity, and induction gives oddness. At modulus four the totient is two; "
                + "the permitted positive periods are one and two. Period one would imply period "
                + "two by adding consecutive differences. The two-step identity excludes either "
                + "period at every onset. This does not settle a bound of twice the totient "
                + "or a general assertion for odd moduli.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala126156"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("bala-a126156-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula CosineFormula()
    {
        var value = new Formula.Fraction(
            Power(Rational(Seq(Minus, D(2))), Apply(Q("Nat", "div"), V("j"), D(2))),
            Rational(Apply(Q("Nat", "factorial"), V("j"))));
        var coefficient = Call("ite", Call("Even", V("j")), value, D(0));
        var function = Parenthesized(Seq(V("j"), Colon, Sp, Naturals(), Sp, Mapsto, Sp, coefficient));
        return Disp(Equality(V("cosSqrtTwo"), Apply(Q("PowerSeries", "mk"), function)));
    }

    private static Formula SourceFormula() => Disp(All("A", Series(), Equality(
        Call("IsSourceEGF", V("A")), Parenthesized(Conjunction(
            Equality(Apply(Q("PowerSeries", "constantCoeff"), V("A")), D(1)),
            Equality(Multiply(Power(V("A"), D(2)), V("cosSqrtTwo")), D(1)))))));

    private static Formula ClaimBody()
    {
        var congruence = ExistsIn("z", Integers(), Equality(
            Subtract(Coefficient(Add(V("n"), V("p"))), Coefficient(V("n"))),
            Multiply(Rational(V("k")), Rational(V("z")))));
        var tail = All("n", Naturals(), Implication(Seq(V("N"), Sp, Le, Sp, V("n")), congruence));
        var divides = Seq(V("p"), Sp, Mid, Sp, Apply(Q("Nat", "totient"), V("k")));
        var period = ExistsIn("N", Naturals(), ExistsIn("p", Naturals(),
            Conjunction(Less(D(0), V("p")), Conjunction(divides, tail))));
        var moduli = All("k", Naturals(), Implication(Less(D(0), V("k")), period));
        return Conjunction(ExistsIn("A", Series(), Call("IsSourceEGF", V("A"))),
            All("A", Series(), Implication(Call("IsSourceEGF", V("A")), moduli)));
    }

    private static Formula Coefficient(Formula n) => Multiply(
        Rational(Apply(Q("Nat", "factorial"), Multiply(D(2), Parenthesized(n)))),
        Apply(Q("PowerSeries", "coeff"), Multiply(D(2), Parenthesized(n)), V("A")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Rational(Formula x) => Parenthesized(Seq(x, Colon, Sp, Rationals()));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(
        Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(V(name))), arguments);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Conjunction(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
    private static Formula Implication(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Equality(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Less(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
}
