using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CubedBinaryProductModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2024a373308");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A373308 at indices 3n+1 and 3n+2 are divisible by three.",
        H("Hanna's Cubed Binary Product Conjecture"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a373308 defines the sequence by "
                + "the expansion of Product_{n>=0} (1-x^(2^n))^3. Here the infinite product "
                + "is represented by its exact defining functional equation A(x) = "
                + "(1-x)^3 A(x^2), with constant coefficient one. Removing the first "
                + "factor and shifting the remaining factors gives this characterization. "
                + "The existence and uniqueness theorems below establish that characterization "
                + "for the recursively constructed series; no infinite-product operator is used.")),
            Paragraph(Text("All indices are natural numbers, and a takes integer values. "
                + "PowerSeries(Z) denotes the formal power-series ring with indeterminate X. "
                + "The notation coeff(i,f) extracts coefficient i, mk constructs a series "
                + "from its coefficient function, and subst(f,g) substitutes g into f. "
                + "Index subtraction is natural subtraction and div is natural-number "
                + "integer division. The finite sum ranges over i in range(n+2). "
                + "The cast in the support theorem is the integer cast into ZMod(3).")),
            Node("a", "The recursive integer coefficients", CoefficientFormula(),
                "The convolution with (1-X)^3 defines each successor coefficient using "
                + "only earlier coefficients. Substitution by X^2 selects even indices. "
                + "The polynomial coefficient is zero beyond degree three, so this is "
                + "the coefficient recurrence of the defining product equation.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The series has coefficient function a and integer coefficients.",
                DescribeRole.Definition),
            Node("generating_equation", "The defining functional equation", EquationFormula(),
                "At degree zero the constant coefficient is one. At every positive degree, "
                + "the product coefficient formula and the coefficient formula for substitution "
                + "by X^2 reproduce exactly the recursive definition."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "Strong induction compares the coefficients of any normalized solution "
                + "with the constructed series. Every coefficient used at a positive degree "
                + "has index at most half that degree and is therefore already equal."),
            Node("mod_three_support", "Support modulo three", SupportFormula(),
                "Map the generating equation to ZMod(3). Frobenius gives (1-X)^3 = 1-X^3. "
                + "In the resulting equation, coefficient n depends only on n/2 when n "
                + "is even, and on (n-3)/2 when n is at least three and n-3 is even. "
                + "If three does not divide n, each contributing predecessor is smaller "
                + "and is also not divisible by three. Strong induction makes both contributions zero."),
            Node("hanna_conjecture", "The A373308 divisibility conjecture", ConjectureFormula(),
                "Neither 3n+1 nor 3n+2 is divisible by three. The support theorem makes "
                + "both integer coefficients zero in ZMod(3), which is equivalent to "
                + "integer divisibility by three. The conjecture is the one quoted in "
                + "hanna2024a373308.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a373308-cubed-binary-product-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a373308-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => F.Id("n");
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
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
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Cubic() => Power(Subtract(D(1), X()), D(3));
    private static Formula RightSide(Formula series) =>
        Mul(Cubic(), Call("subst", series, Power(X(), D(2))));

    private static Formula CoefficientFormula()
    {
        Formula i = F.Id("i");
        Formula index = Parenthesized(Subtract(Add(N(), D(1)), i));
        Formula selected = Parenthesized(Seq(Named("if"), Sp,
            Parenthesized(Divides(D(2), index)), Sp, Named("then"), Sp,
            Call("a", Call("div", index, D(2))), Sp, Named("else"), Sp, D(0)));
        Formula summand = Mul(Call("coeff", i, Cubic()), selected);
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(i, Sp, InMacro, Sp, Call("range", Add(N(), D(2))))),
            Sp, Parenthesized(summand));
        return Disp(new Formula.Aligned([
            Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
            Equal(Call("a", D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(Call("a", Add(N(), D(1))), sum))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Equal(
        Seq(Generating(), Colon, Sp, Call("PowerSeries", Integers())), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", Generating()), D(1)),
        Equal(Generating(), RightSide(Generating()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equal(b, RightSide(b)), Equal(b, Generating())))));
    }

    private static Formula SupportFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(Neg, Sp, Parenthesized(Divides(D(3), N()))),
            Equal(Call("cast", Call("a", N()), Call("ZMod", D(3))), D(0)))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()), And(
        Divides(D(3), Call("a", Add(Mul(D(3), N()), D(1)))),
        Divides(D(3), Call("a", Add(Mul(D(3), N()), D(2)))))));
}
