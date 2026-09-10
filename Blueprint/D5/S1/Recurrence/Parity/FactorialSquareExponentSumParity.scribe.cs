using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class FactorialSquareExponentSumParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a222014");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A222014 are odd exactly one below a power of two.",
        H("Factorial Square-Exponent Sum Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a222014 defines A by a factorial "
                + "product sum whose numerator exponent is r squared and whose denominator "
                + "exponent is r. It asks whether a(n) is odd exactly when n+1 is a power "
                + "of two.")),
            Paragraph(Text("All indices are natural numbers. R is a commutative ring, Z is "
                + "the integer ring, and X is the power-series indeterminate. The operation "
                + "coeff extracts coefficients, mk constructs a series from its coefficient "
                + "function, and C embeds a scalar as a constant series. Each displayed unit "
                + "inverse has constant coefficient one.")),
            Paragraph(Text("The parameter functions e and d control the numerator and "
                + "denominator powers independently. The factor X to the r makes the degree "
                + "window independent of their growth. P denotes the private finite-step "
                + "approximations used to define a, pi is the integer cast into ZMod(2), and "
                + "K is the Catalan series from CatalanCompositionSquareParity.")),
            Node("parameterizedTerm", "The exponent-parametric summand", ParameterizedTermFormula(),
                "The two exponent functions are arbitrary. The product ranges over k below r, "
                + "so its scalar k+1 represents the factors numbered one through r.",
                DescribeRole.Definition),
            Node("parameterized_term_coeff_eq_zero", "Uniform degree contraction",
                ParameterizedVanishingFormula(),
                "The factor X to the r divides every parameterized summand. The coefficient "
                + "criterion for this divisibility makes every degree below r zero."),
            Node("term", "The A222014 summand", TermFormula(),
                "Set e(r) to r squared and set d(r,k) to r in the parameterized summand.",
                DescribeRole.Definition),
            Node("term_coeff_eq_zero", "The A222014 coefficient window", VanishingFormula(),
                "The square-exponent specialization inherits the uniform coefficient window."),
            Node("a", "The coefficient sequence", SequenceFormula(),
                "Starting from the zero series, each finite step extends agreement by one "
                + "degree. The diagonal coefficient at stage n+1 defines a(n).",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The series is constructed from the diagonal coefficient function.",
                DescribeRole.Definition),
            Node("generating_equation", "The coefficientwise OEIS equation", EquationFormula(),
                "Stability identifies each diagonal coefficient with one further finite step. "
                + "Only indices at most N contribute to degree N."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "A fixed point agrees with A below degree zero. The degree contraction extends "
                + "agreement one coefficient at a time, yielding equality."),
            Node("mod_two_equation", "The reduced quadratic equation", ModTwoEquationFormula(),
                "For r at least two, the scalar r factorial is zero in ZMod(2). The terms r=0 "
                + "and r=1 remain, and cancellation of their unit denominator gives the "
                + "quadratic equation."),
            Node("mod_two_identity", "Catalan series identity", ModTwoIdentityFormula(),
                "The reduced A222014 and A222013 series have constant coefficient one and obey "
                + "the same quadratic equation. Unit cancellation identifies them, after which "
                + "the established A222013 identity supplies X map(pi,A)=map(pi,K)."),
            Node("hanna_conjecture", "Hanna's parity conjecture", HannaFormula(),
                "Coefficient equality transfers the established A222013 parity theorem to a. "
                + "An integer maps to one in ZMod(2) exactly when it is odd.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("a222014-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Ring() => F.Id("R");
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula IntegerSeries() => Series(Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula K() => F.Id("K");
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
    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, Rightarrow, Sp, target);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Reduce(Formula series) => Call("map", F.Id("pi"), series);

    private static Formula Product(Formula r, Formula f, Formula exponent)
    {
        Formula k = F.Id("k");
        Formula factor = Add(D(1), Mul(Mul(Call("C", Add(k, D(1))), X()),
            Power(f, exponent)));
        return Seq(new Formula.Subscript(Prod,
            Seq(k, Sp, InMacro, Sp, Call("range", r))), Sp, Parenthesized(factor));
    }

    private static Formula ParameterizedTermFormula()
    {
        Formula e = F.Id("e");
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula k = F.Id("k");
        Formula f = F.Id("F");
        Formula exponent = Call("d", r, k);
        Formula numerator = Mul(Mul(Call("C", Call("factorial", r)), Power(X(), r)),
            Power(f, Call("e", r)));
        Formula value = Mul(numerator, Call("invOfUnit", Product(r, f, exponent), D(1)));
        return Disp(Seq(Bound("e", Arrow(Naturals(), Naturals())),
            Bound("d", Arrow(Naturals(), Arrow(Naturals(), Naturals()))),
            Bound("r", Naturals()), Bound("F", Series(Ring())),
            Equal(Call("parameterizedTerm", e, d, r, f), value)));
    }

    private static Formula ParameterizedVanishingFormula()
    {
        Formula e = F.Id("e");
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula n = F.Id("N");
        Formula f = F.Id("F");
        return Disp(Seq(Bound("e", Arrow(Naturals(), Naturals())),
            Bound("d", Arrow(Naturals(), Arrow(Naturals(), Naturals()))),
            Bound("r", Naturals()), Bound("N", Naturals()),
            Implication(Seq(n, Sp, Lt, Sp, r), Seq(Bound("F", Series(Ring())),
                Equal(Call("coeff", n, Call("parameterizedTerm", e, d, r, f)), D(0))))));
    }

    private static Formula TermFormula()
    {
        Formula r = F.Id("r");
        Formula f = F.Id("F");
        Formula numerator = Mul(Mul(Call("C", Call("factorial", r)), Power(X(), r)),
            Power(f, Power(r, D(2))));
        Formula value = Mul(numerator, Call("invOfUnit", Product(r, f, r), D(1)));
        return Disp(Seq(Bound("r", Naturals()), Bound("F", IntegerSeries()),
            Equal(Call("term", r, f), value)));
    }

    private static Formula VanishingFormula() => Disp(Seq(
        Bound("r", Naturals()), Bound("N", Naturals()),
        Implication(Seq(F.Id("N"), Sp, Lt, Sp, F.Id("r")),
            Seq(Bound("F", IntegerSeries()), Equal(Call("coeff", F.Id("N"),
                Call("term", F.Id("r"), F.Id("F"))), D(0))))));

    private static Formula Window(Formula n, Formula series) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("r"), Sp, InMacro, Sp,
            Call("range", Add(n, D(1))))), Sp,
        Parenthesized(Call("coeff", n, Call("term", F.Id("r"), series))));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("a", n),
            Call("coeff", n, Call("P", Add(n, D(1)))))));
    }

    private static Formula CoefficientEquation(Formula series) =>
        Seq(Bound("N", Naturals()), Equal(Call("coeff", F.Id("N"), series),
            Window(F.Id("N"), series)));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(1)), CoefficientEquation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", IntegerSeries()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(CoefficientEquation(b), Equal(b, A())))));
    }

    private static Formula ModTwoEquationFormula() => Disp(Equal(Reduce(A()),
        Add(D(1), Mul(X(), Power(Reduce(A()), D(2))))));

    private static Formula ModTwoIdentityFormula() => Disp(Equal(
        Mul(X(), Reduce(A())), Reduce(K())));

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(Add(n, D(1)), Power(D(2), k)));
        return Disp(Seq(Bound("n", Naturals()), Call("Odd", Call("a", n)),
            Sp, Iff, Sp, Parenthesized(support)));
    }
}
