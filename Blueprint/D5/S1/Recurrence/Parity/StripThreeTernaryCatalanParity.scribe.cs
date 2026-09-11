using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class StripThreeTernaryCatalanParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a378578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A378578 have ternary Catalan parity.",
        H("Strip-Three Ternary Catalan Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a378578 defines A by removing "
                + "every factor of three from the coefficients of 1+xA(x)^3. It conjectures "
                + "that a(n) and binomial(3n,n)/(2n+1) have the same parity for every natural n.")),
            Paragraph(Text("PowerSeries(Z) is the integer formal power-series ring and X "
                + "is its indeterminate. The functions coeff and constantCoeff extract "
                + "coefficients, and mk constructs a series from its coefficient function. "
                + "The notation div denotes integer division, with natural division on "
                + "natural arguments; mod is remainder. Natural subtraction is truncated. "
                + "The function intCast embeds a natural number into Z, and cast2 sends "
                + "an integer or natural number to ZMod(2). The notation intCastRingHom "
                + "denotes Lean's Int.castRingHom. The symbols approximation "
                + "and step below describe the private construction of a.")),
            Node("strip3", "Removing powers of three", StripFormula(),
                "The divisor is three to the integer's three-adic valuation. This divides "
                + "every integer, including zero. The valuation of zero is zero, so strip3(0)=0.",
                DescribeRole.Definition),
            Node("strip3_mod_two", "Stripping preserves parity", StripParityFormula(),
                "Multiply strip3(m) by the removed power of three to recover m. In ZMod(2) "
                + "that power is one, so the two integers have equal images."),
            Node("strip3Series", "Coefficientwise stripping", StripSeriesFormula(),
                "Apply strip3 separately to every coefficient.", DescribeRole.Definition),
            Node("a", "The stabilized coefficient sequence", CoefficientFormula(),
                "The initial approximation is one. Multiplication by X makes the next "
                + "coefficient depend only on preceding coefficients. Thus agreement below "
                + "degree d improves to agreement below degree d+1 after applying step. "
                + "The coefficient of degree n stabilizes by approximation n+1.",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The defining functional equation", EquationFormula(),
                "Stability of the diagonal coefficients proves the fixed-point equation. "
                + "The constant coefficient is strip3(1)=1."),
            Node("generating_unique", "Uniqueness of the generating series", UniqueFormula(),
                "The constant coefficients agree. Induction using the degree contraction "
                + "then makes every coefficient agree with generatingSeries."),
            Node("choose_three_lucas", "Lucas recursions", LucasFormula(),
                "Lucas's theorem at the prime two removes the last binary digits. "
                + "The even case takes one step, the residue-one case takes two steps, "
                + "and the residue-three case contains the vanishing factor choose(0,1)."),
            Node("ternary_catalan_div", "Exact division at positive indices", DivisionFormula(),
                "The adjacent-binomial identity gives n choose(3n,n) = "
                + "(2n+1) choose(3n,n-1). For positive n it implies "
                + "2 choose(3n,n-1) <= choose(3n,n). Multiplying the displayed natural "
                + "difference by 2n+1 gives choose(3n,n), proving the quotient identity."),
            Node("mod_two_identity", "The reduced generating series", ModTwoFormula(),
                "Stripping preserves parity, so the mapped series F satisfies F=1+XF^3. "
                + "Multiplication by F and characteristic two give F=F^2+XF^4. "
                + "Frobenius expresses squares by substitution of X^2. The coefficient "
                + "at 2r repeats that at r, the coefficient at 4r+1 repeats that at r, "
                + "and the coefficient at 4r+3 vanishes. With constant coefficient one, "
                + "strong induction and the Lucas recursions determine every coefficient."),
            Node("hanna_conjecture", "Hanna's parity conjecture", HannaFormula(),
                "The reduced series gives the parity of choose(3n,n). For positive n "
                + "the exact quotient differs from this binomial coefficient by twice "
                + "a natural number. At n=0 the quotient and the binomial coefficient "
                + "are both one. Converting equality in ZMod(2) to integer remainders "
                + "proves the conjecture for every natural n.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378578-strip-three-ternary-catalan-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a378578-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula N() => F.Id("n");
    private static Formula A() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Cast2(Formula value) => Call("cast2", value);
    private static Formula Choose(Formula n) => Call("choose", Mul(D(3), Parenthesized(n)), n);
    private static Formula Denominator() => Add(Mul(D(2), N()), D(1));
    private static Formula Quotient() => Call("div", Choose(N()), Denominator());
    private static Formula Step(Formula value) =>
        Call("strip3Series", Add(D(1), Mul(F.Id("X"), Power(value, D(3)))));
    private static Formula Equation(Formula value) => Equal(value, Step(value));

    private static Formula StripFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(Bound("m", Integers()), Equal(Call("strip3", m),
            Call("div", m, Power(D(3), Call("padicValInt", D(3), m))))));
    }

    private static Formula StripParityFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(Bound("m", Integers()),
            Equal(Cast2(Call("strip3", m)), Cast2(m))));
    }

    private static Formula StripSeriesFormula()
    {
        Formula f = F.Id("F");
        return Disp(Seq(Bound("F", Series()), Equal(Call("strip3Series", f),
            Call("mk", Lambda("n", Naturals(), Call("strip3", Call("coeff", N(), f)))))));
    }

    private static Formula CoefficientFormula()
    {
        Formula d = F.Id("d");
        Formula f = F.Id("F");
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Call("coeff", N(), Call("approximation", Add(N(), D(1)))))),
            Equal(Call("approximation", D(0)), D(1)),
            Seq(Bound("d", Naturals()), Equal(Call("approximation", Add(d, D(1))),
                Call("step", Call("approximation", d)))),
            Seq(Bound("F", Series()), Equal(Call("step", f), Step(f)))
        ]));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(1)), Equation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula LucasFormula()
    {
        Formula r = F.Id("r");
        return Disp(Seq(Bound("r", Naturals()), Conjunction(
            Equal(Cast2(Choose(Mul(D(2), r))), Cast2(Choose(r))), Conjunction(
                Equal(Cast2(Choose(Add(Mul(D(4), r), D(1)))), Cast2(Choose(r))),
                Equal(Cast2(Choose(Add(Mul(D(4), r), D(3)))), D(0))))));
    }

    private static Formula DivisionFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(0), Sp, Lt, Sp, N()), Equal(Quotient(),
            Subtract(Choose(N()), Mul(D(2),
                Call("choose", Mul(D(3), N()), Subtract(N(), D(1)))))))));

    private static Formula ModTwoFormula() => Disp(Equal(
        Call("map", Call("intCastRingHom", Call("ZMod", D(2))), A()),
        Call("mk", Lambda("n", Naturals(), Cast2(Choose(N()))))));

    private static Formula HannaFormula() => Disp(Seq(Bound("n", Naturals()), Equal(
        new Formula.Modulo(Call("a", N()), D(2)),
        new Formula.Modulo(Call("intCast", Quotient()), D(2)))));
}
