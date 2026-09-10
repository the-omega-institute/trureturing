using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class DiagonalPowerRatioAllOddDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a397241");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient of the normalized series in OEIS A397241 is odd.",
        H("Diagonal Power Ratios and Odd Coefficients"),
        Blocks(
            Paragraph(Text("The generating equation and oddness conjecture are recorded in "
                + "hanna2026a397241. Write A for generatingSeries and P(r) for approximation(r). "
                + "The coefficients a(n), the series A, the approximations P(r), and the "
                + "comparison series B are over the integers. Indices and exponents are "
                + "natural numbers. Multipliers such as n-1 are integer subtraction after "
                + "casting n, as in the Lean declaration.")),
            Paragraph(Text("The operator coeff(n,f) extracts the degree-n coefficient, and mk "
                + "forms a power series from a coefficient function. The operator map applies "
                + "a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes "
                + "Int.castRingHom(ZMod(2)). Both sides of the reduction identity are series "
                + "over ZMod(2), and the constant function in its right-hand side takes value "
                + "one in ZMod(2).")),
            Node("a", "Construction of the integer coefficients", CoefficientDefinition(),
                "Starting from the constant series one, each approximation fixes coefficients "
                + "zero and one at one and subtracts the diagonal equation residual at every "
                + "higher degree. Agreement below degree n implies agreement through degree n "
                + "after this correction. Thus the displayed diagonal coefficients stabilize.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The coefficient function a defines the formal integer power series A.",
                DescribeRole.Definition),
            Node("generating_equation", "The normalized defining equation",
                Disp(Conjunction(Equal(Coefficient(D(0), A()), D(1)),
                    Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A())))),
                "For unit-constant series agreeing below degree n, the difference of the "
                + "degree-n coefficients of their m-th powers is m times their degree-n "
                + "coefficient difference. In the equation residual the multiplier is "
                + "n squared minus (n-1)(n+1), which is one. Stabilization therefore gives "
                + "a fixed point of the correction, and its residuals vanish."),
            Node("generating_unique", "Uniqueness of the normalized integer series",
                UniqueFormula(),
                "Strong induction on the degree compares any normalized solution B with A. "
                + "Their residuals vanish, so the multiplier-one identity forces equality "
                + "of the next coefficient. The two normalization hypotheses start the induction."),
            Node("central_binom_even", "Evenness of central binomial coefficients",
                Disp(Seq(Bound("m", Naturals()),
                    Implication(Less(D(0), M()),
                        Divides(D(2), Call("choose", Mul(D(2), M()), M()))))),
                "This is Mathlib's two_dvd_centralBinom_of_one_le, expressed using choose."),
            Node("mod_two_identity", "The reduction is the all-ones series",
                Disp(Equal(Reduce(A()), Call("mk", Lambda("n", D(1))))),
                "The coefficient of degree n in the (n+1)-st power of the all-ones series "
                + "is choose(2n,n), which is even for n greater than one. For even n the "
                + "remaining multiplier vanishes modulo two. For odd n=2m+1 greater than "
                + "one, the other coefficient is choose(4m+1,2m); Lucas reduction modulo two "
                + "gives choose(2m,m), which is even. The all-ones series therefore satisfies "
                + "the reduced equation. The same coefficient induction proves uniqueness "
                + "over ZMod(2), giving the identity."),
            Node("hanna_conjecture", "Hanna's oddness conjecture",
                Disp(Seq(Bound("n", Naturals()), Call("Odd", Call("a", N())))),
                "Extracting any coefficient of the reduction identity gives a(n)=1 in "
                + "ZMod(2). Mathlib's integer-cast criterion identifies this with oddness "
                + "of the integer a(n), including degrees zero and one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397241-diagonal-power-ratio-all-odd"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397241-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Reduce(Formula f) =>
        Call("map", Call("intCast", Call("ZMod", D(2))), f);
    private static Formula DiagonalLeft(Formula f, Formula n) =>
        Mul(n, Coefficient(n, Power(f, n)));
    private static Formula DiagonalRight(Formula f, Formula n) =>
        Mul(Parenthesized(Subtract(n, D(1))), Coefficient(n, Power(f, Add(n, D(1)))));
    private static Formula Equation(Formula f) => Seq(Bound("n", Naturals()),
        Implication(Less(D(1), N()), Equal(DiagonalLeft(f, N()), DiagonalRight(f, N()))));

    private static Formula CoefficientDefinition()
    {
        var r = F.Id("r");
        var k = F.Id("k");
        var p = Call("P", r);
        var residual = Subtract(DiagonalLeft(p, k), DiagonalRight(p, k));
        var next = Seq(Named("if"), Sp, k, Sp, Le, Sp, D(1), Sp, Named("then"), Sp,
            D(1), Sp, Named("else"), Sp,
            Subtract(Coefficient(k, p), Parenthesized(residual)));
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("r", Naturals()),
                Equal(Call("P", Add(r, D(1))), Call("mk", Lambda("k", next)))),
            Seq(Bound("n", Naturals()),
                Equal(Call("a", N()), Coefficient(N(), Call("P", Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }
}
