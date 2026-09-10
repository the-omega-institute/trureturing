using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CubicNinthPowerSubstitutionModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CubicNinthPowerSubstitutionModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2023a363560");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive coefficient index outside the class one modulo seven in OEIS A363560 has coefficient divisible by three.",
        H("Hanna's Cubic Generating Equation Modulo Three"),
        Blocks(
            Paragraph(Text("The generating equation and conjecture are recorded in "
                + "hanna2023a363560. Write A for generatingSeries and U(k) for the "
                + "auxiliary integer power-series approximations. All indices and "
                + "exponents are natural numbers; X is the indeterminate. The operator "
                + "coeff(n,f) extracts the degree-n coefficient, constantCoeff extracts "
                + "the constant coefficient, and mk forms a series from its coefficient "
                + "function. The remainder of n modulo seven is a natural-number remainder.")),
            Node("a", "The stabilized integer coefficients", CoefficientDefinition(),
                "Multiplication by X raises coefficient agreement by one degree, "
                + "while evaluating the displayed polynomial preserves agreement. "
                + "Thus the degree-n coefficient has stabilized by approximation n+1.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "A is the integer power series whose degree-n coefficient is a(n).",
                DescribeRole.Definition),
            Node("cubic_iff_fixed", "The integral fixed-point bridge", BridgeFormula(),
                "The polynomial t+t squared+t to the ninth factors as "
                + "(t squared+t+1)(t-t cubed+t to the fourth-t to the sixth+t to the seventh). "
                + "Subtracting the two sides of the cubic equation therefore gives "
                + "(B squared+B+1)(B-1-X P(B))=0, where P is the polynomial in the "
                + "displayed fixed-point equation. The first factor has constant "
                + "coefficient three and is nonzero. Integer power series have no "
                + "zero divisors, so cancellation proves the equivalence."),
            Node("generating_equation", "The normalized cubic equation",
                Disp(Conjunction(Equal(Constant(A()), D(1)), Cubic(A()))),
                "The stabilized approximations give the integral fixed-point identity "
                + "and constant coefficient one. The bridge then gives the exact "
                + "cubic generating equation."),
            Node("generating_unique", "Uniqueness of the normalized integer solution",
                UniqueFormula(),
                "The bridge turns any normalized cubic solution into a fixed point "
                + "of the same polynomial operator. Induction on degree, using the "
                + "extra factor X, proves agreement of every coefficient."),
            Node("hanna_conjecture", "The A363560 divisibility conjecture",
                ConjectureFormula(),
                "Reduce the integral fixed-point identity modulo three and subtract "
                + "one, writing B for the reduced series minus one. The polynomial "
                + "identity P(1+B)=1+B to the seventh in characteristic three gives "
                + "B=X(1+B to the seventh). Below a fixed degree, convolution adds "
                + "the residue classes of coefficient indices: the kth power of "
                + "a series supported on class one is supported on class k modulo "
                + "seven. Strong induction now shows that B vanishes outside class "
                + "one. At positive degrees A and B have the same reduced coefficients, "
                + "which proves divisibility by three.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a363560-cubic-ninth-power-substitution-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a363560-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula Polynomial(Formula f) =>
        Add(Subtract(Add(Subtract(f, Power(f, D(3))), Power(f, D(4))),
            Power(f, D(6))), Power(f, D(7)));
    private static Formula Step(Formula f) =>
        Add(D(1), Multiply(X(), Parenthesized(Polynomial(f))));
    private static Formula Fixed(Formula f) => Equal(f, Step(f));
    private static Formula Cubic(Formula f) =>
        Equal(Power(f, D(3)), Add(D(1), Multiply(X(),
            Parenthesized(Add(Add(f, Power(f, D(2))), Power(f, D(9)))))));

    private static Formula CoefficientDefinition()
    {
        var k = F.Id("k");
        return Disp(new Formula.Aligned([
            Equal(Call("U", D(0)), D(1)),
            Seq(Bound("k", Naturals()), Equal(Call("U", Add(k, D(1))), Step(Call("U", k)))),
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Coefficient(N(), Call("U", Add(N(), D(1))))))
        ]));
    }

    private static Formula BridgeFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Constant(b), D(1)),
                Parenthesized(Seq(Parenthesized(Cubic(b)), Sp, Iff, Sp,
                    Parenthesized(Fixed(b)))))));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Constant(b), D(1)),
                Implication(Cubic(b), Equal(b, A())))));
    }

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(0), Sp, Lt, Sp, N()),
            Implication(Seq(new Formula.Modulo(N(), D(7)), Sp, Neq, Sp, D(1)),
                Seq(D(3), Sp, Mid, Sp, Call("a", N()))))));
}
