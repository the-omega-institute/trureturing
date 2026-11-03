using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteTieGeneratingFunctionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/sheppard2025a381737");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary rational generating function of the complete increasing enumeration of physicists Hermite absolute-tie orders.",
        H("The Hermite absolute-tie generating function"),
        Blocks(
            Paragraph(Text("The order k and every exponent are natural numbers, including zero. The predicate HasExactlyTwo is the full-row condition from HermiteAbsoluteTieOrders: every exponent from zero through k is compared, including parity-zero coefficients. The enumeration index starts at one. All displayed series are formal power series over the rationals; no analytic convergence assertion is made.")),
            Node("P", "The numerator polynomial", Equal(F.Id("P"), Numerator()),
                "The numerator is exactly 8X+5X squared+5X cubed-X to the fourth-X to the fifth.", DescribeRole.Definition),
            Node("D", "The denominator polynomial", Equal(F.Id("D"), Denominator()),
                "The denominator is (1-X) cubed times (1+X) squared and has constant coefficient one.", DescribeRole.Definition),
            Node("claim", "The complete generating-function assertion", Equal(F.Id("claim"), ClaimBody()),
                "There is a positive, strictly increasing natural enumeration of every order with exactly two absolute maxima. Its zero-padded rational formal series has constant coefficient zero, coefficient a(n) at every positive index, and equals the literal numerator times the inverse of the literal denominator. The equality is in formal power series, not an analytic identity." , DescribeRole.Definition),
            Node("result", "The full A381737 Conjecture 3 generating function", ClaimBody(),
                "Reuse HermiteAbsoluteTieOrders.result for the exhaustive positive enumeration. Construct the series from the three standard binomial series T0=1/(1-X), T1=1/(1-X) squared, and T2=1/(1-X) cubed, together with the rescaled series T1(-X). The combination 4T2-2T1-2T0-T1(-X)+1 has zero constant coefficient and has coefficient 2n(n+2)+(n+1)(-1)^(n+1) at every positive n. The standard binomial identities give the product with (1-X) cubed(1+X) squared equal to the numerator; constant coefficient one then permits the formal inverse. Natural-number casts are discharged from the positivity of the existing integer formula. The statement is over all k and all positive n and contains no finite prefix, selected subfamily, recurrence proxy, a0 extension, or convergence condition.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a381737-hermite-tie-generating-function"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hermite-tie-generating-function-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, FormulaDsl.Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, Par(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Sp, Minus, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Par(a), Sp, FormulaDsl.Iff, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, F.Id(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, F.Id(n), Colon, Sp, t, Comma, Sp, b);
    private static Formula Cast(Formula a, Formula t) => Par(Seq(a, Colon, Sp, t));
    private static Formula Coeff(Formula n, Formula s) => Call("coeff", n, s);
    private static Formula Constant(Formula s) => Call("constantCoeff", s);
    private static Formula Numerator() => Sub(Sub(Add(Add(Mul(D(8), F.Id("X")), Mul(D(5), Pow(F.Id("X"), D(2)))), Mul(D(5), Pow(F.Id("X"), D(3)))), Pow(F.Id("X"), D(4))), Pow(F.Id("X"), D(5)));
    private static Formula Denominator() => Mul(Pow(Sub(D(1), F.Id("X")), D(3)), Pow(Add(D(1), F.Id("X")), D(2)));
    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var m = F.Id("m"); var k = F.Id("k"); var a = F.Id("a"); var s = F.Id("S");
        var positive = All("n", Nat(), Arrow(Seq(D(1), Sp, Le, Sp, n), Seq(D(0), Sp, Lt, Sp, Call("a", n))));
        var increasing = All("n", Nat(), All("m", Nat(), Arrow(Seq(D(1), Sp, Le, Sp, n), Arrow(Seq(n, Sp, Lt, Sp, m), Seq(Call("a", n), Sp, Lt, Sp, Call("a", m))))));
        var unique = Some("n", Nat(), And(And(Seq(D(1), Sp, Le, Sp, n), Eq(Call("a", n), k)), All("m", Nat(), Arrow(And(Seq(D(1), Sp, Le, Sp, m), Eq(Call("a", m), k)), Eq(m, n)))));
        var enumeration = All("k", Nat(), Iff(Call("HasExactlyTwo", k), unique));
        var series = And(Eq(Coeff(D(0), s), D(0)), And(All("n", Nat(), Arrow(Seq(D(1), Sp, Le, Sp, n), Eq(Coeff(n, s), Cast(Call("a", n), Rationals())))), And(Eq(Constant(F.Id("D")), D(1)), Eq(s, Mul(F.Id("P"), Pow(F.Id("D"), Seq(Minus, D(1))))))));
        return Some("a", Seq(Nat(), Sp, To, Sp, Nat()), And(positive, And(increasing, And(enumeration, Some("S", Series(), series)))));
    }
}
