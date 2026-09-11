using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CubicTernarySubstitutionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2024a375439");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd coefficients of OEIS A375439 occur exactly at powers of three and twice powers of three.",
        H("Hanna's Cubic Ternary Substitution Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a375439 defines A(x) by "
                + "A(x)=x+x^2+(2A(x)^3+A(x^3))/3 and conjectures its parity support. "
                + "The integer series below has constant coefficient zero and satisfies "
                + "that equation after multiplication by three.")),
            Paragraph(Text("All indices are natural numbers. PowerSeries(Z) denotes the "
                + "integer formal power-series ring, X its indeterminate, and powers are "
                + "ordinary ring powers. The notation subst(B,C) means substitution of C "
                + "into B. The operator coeff(n,B) extracts a coefficient, mk constructs a "
                + "series from its coefficient function, and div is integer Euclidean "
                + "division. Multiplication by a natural number denotes repeated addition. "
                + "The map rho reduces every integer coefficient to ZMod(3).")),
            Node("cube_congr_subst_three", "Cubic Frobenius congruence", CubeFormula(),
                "Mathlib's multivariate power-series Frobenius identity identifies expansion "
                + "by three with cubing after reduction modulo three. Frobenius is the "
                + "identity on ZMod(3). Thus every coefficient of 2B^3+B(X^3) is divisible "
                + "by three, for every integer series B."),
            Node("a", "The stabilized integer coefficients", CoefficientFormula(),
                "The auxiliary approximation starts at zero and repeatedly applies the "
                + "displayed transformation. Each division by three is exact by the "
                + "Frobenius congruence. For series with zero constant coefficient, agreement "
                + "below degree d improves to agreement below degree d+1. Coefficient n "
                + "has therefore stabilized at approximation n+1.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The generating series is the integer power series with coefficient function a.",
                DescribeRole.Definition),
            Node("generating_equation", "The defining OEIS equation", EquationFormula(),
                "The stabilized series agrees to every finite degree with later approximations. "
                + "Degree contraction makes it a fixed point. Exact division then gives "
                + "the displayed integer identity and the zero constant coefficient."),
            Node("generating_unique", "Uniqueness with zero constant coefficient", UniqueFormula(),
                "The integer equation first implies that B is a fixed point of the same "
                + "transformation. Induction on the degree of coefficient agreement then "
                + "identifies B with generatingSeries."),
            Node("hanna_conjecture", "The A375439 parity conjecture", HannaFormula(),
                "Reducing the coefficient equation modulo two removes the cubic term. "
                + "The coefficients at indices one and two are odd. At every larger "
                + "positive index, oddness is equivalent to divisibility of the index by "
                + "three and oddness at one third of that index. Strong induction gives "
                + "exactly the two displayed families.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a375439-cubic-ternary-substitution-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a375439-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula Numerator(Formula series) =>
        Add(Mul(D(2), Power(series, D(3))), Call("subst", series, Power(X(), D(3))));
    private static Formula BaseSeries() => Add(X(), Power(X(), D(2)));
    private static Formula Equation(Formula series) => Equal(Mul(D(3), series),
        Add(Add(Mul(D(3), Parenthesized(BaseSeries())), Mul(D(2), Power(series, D(3)))),
            Call("subst", series, Power(X(), D(3)))));

    private static Formula CubeFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()), Equal(Call("rho", Power(b, D(3))),
            Call("rho", Call("subst", b, Power(X(), D(3)))))));
    }

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula j = F.Id("j");
        Formula next = Add(BaseSeries(), Call("mk", Parenthesized(Seq(
            j, Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Call("div", Call("coeff", j, Parenthesized(Numerator(Approx(d)))), D(3))))));
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Call("coeff", n, Approx(Add(n, D(1)))))),
            Equal(Approx(D(0)), D(0)),
            Seq(Bound("d", Naturals()), Equal(Approx(Add(d, D(1))), next))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", F.Id("a"))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", Generating()), D(0)), Equation(Generating())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equation(b), Equal(b, Generating())))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(Seq(Equal(n, Power(D(3), k)), Sp, Lor, Sp,
                Equal(n, Mul(D(2), Power(D(3), k))))));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Le, Sp, n),
                Parenthesized(Seq(Call("Odd", Call("a", n)), Sp, Iff, Sp, Parenthesized(support))))));
    }
}
