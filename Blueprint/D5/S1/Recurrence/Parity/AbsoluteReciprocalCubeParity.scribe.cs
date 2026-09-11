using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class AbsoluteReciprocalCubeParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/AbsoluteReciprocalCubeParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a380709");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A380709 have Hanna's conjectured binomial parity.",
        H("Absolute Reciprocal Cubes and Binomial Parity"),
        Blocks(
            Paragraph(Text("The generating equation and conjecture are recorded in "
                + "hanna2025a380709. Write A for generatingSeries. The series A, B, F, "
                + "and P(r) have integer coefficients, X is the indeterminate, and "
                + "n and r are natural numbers. The auxiliary series Q and H used in "
                + "the proof have coefficients in ZMod(2).")),
            Paragraph(Text("The operator mk forms a power series from its coefficient "
                + "function, coeff(n,F) extracts its degree-n coefficient, and abs "
                + "is integer absolute value. The operator invOfUnit(F,1) is Mathlib's "
                + "power-series inverse with unit parameter 1. The operator map applies "
                + "a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes "
                + "Int.castRingHom(ZMod(2)). The operator choose is Nat.choose, with "
                + "natural subtraction in its upper index. The operator ofNat denotes "
                + "Int.ofNat and embeds a natural "
                + "number into the integers, while zmodCast embeds it into ZMod(2). "
                + "Remainders in lucas_recursion_q are natural remainders; those in "
                + "hanna_conjecture are integer remainders.")),
            Node("absSeries", "Coefficientwise absolute value", AbsoluteDefinition(),
                "Absolute value is applied to each reciprocal coefficient before cubing.",
                DescribeRole.Definition),
            Node("a", "The stabilized coefficient sequence", SequenceDefinition(),
                "The auxiliary approximations P start at one. Inversion of series "
                + "with constant coefficient one, coefficientwise absolute value, and "
                + "cubing preserve coefficient agreement. Multiplication by X increases "
                + "the degree of agreement, so coefficient n stabilizes by step n+1.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The series A has the stabilized integer coefficients a(n).",
                DescribeRole.Definition),
            Node("generating_equation", "The exact functional equation",
                Disp(Conjunction(Equal(Constant(A()), D(1)), Equation(A()))),
                "Stabilization proves the functional equation with constant "
                + "coefficient one. The inverse is therefore the reciprocal of A."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "The two fixed-point equations extend agreement by one degree. "
                + "Induction gives agreement in every degree and hence equality."),
            Node("lucas_recursion_q", "Three Lucas recursions", LucasFormula(),
                "Mathlib's binary Lucas congruence gives the two odd-index formulas. "
                + "For a positive even index, repeated halving reduces choose(4r,r) "
                + "to a binomial coefficient with even upper and odd lower index, "
                + "which vanishes modulo two."),
            Node("mod_two_identity", "Identification with the binomial parity series",
                ReductionFormula(),
                "Absolute values disappear modulo two. If f is the reduction of A "
                + "and U its reciprocal, the equation gives U=1+X*U^4 and "
                + "f=f^2+X*U^2. The Lucas recursions and Frobenius give "
                + "Q=1+X*Q^4 when coefficient n of Q is choose(4n+1,n) modulo two. "
                + "Factoring the difference of "
                + "the quartic equations gives Q=U by cancellation of a series with "
                + "unit constant coefficient. The two Lucas recursions for the "
                + "displayed binomial series H give H=H^2+X*Q^2. Thus "
                + "(1-f-H)*(f-H)=0. The first factor has constant coefficient -1 "
                + "and is a unit, proving f=H."),
            Node("a_zero", "The constant coefficient",
                Disp(Equal(Call("a", D(0)), D(1))),
                "The exact equation gives a(0)=1. This represents the convention "
                + "binomial(-1,0)=1 without using natural subtraction at index zero."),
            Node("hanna_conjecture", "Hanna's A380709 conjecture", ConjectureFormula(),
                "At each positive index, coefficient extraction from the reduction "
                + "identity gives equality in ZMod(2). Mathlib identifies this "
                + "equality with equality of the two integer remainders modulo two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380709-absolute-reciprocal-cube-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a380709-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula R() => F.Id("r");
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
    private static Formula Mod(Formula value) => new Formula.Modulo(value, D(2));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Named("if"), Sp, Parenthesized(condition), Sp,
            Named("then"), Sp, yes, Sp, Named("else"), Sp, no));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula Step(Formula f) => Add(D(1),
        Mul(X(), Power(Call("absSeries", Call("invOfUnit", f, D(1))), D(3))));
    private static Formula Equation(Formula f) => Equal(f, Step(f));
    private static Formula Reduce(Formula f) =>
        Call("map", Call("intCast", Call("ZMod", D(2))), f);
    private static Formula QChoose(Formula n) => Call("choose", Add(Mul(D(4), n), D(1)), n);
    private static Formula HChoose(Formula n) => Call("choose", Subtract(Mul(D(4), n), D(1)), n);

    private static Formula AbsoluteDefinition() => Disp(Seq(Bound("F", Series()),
        Equal(Call("absSeries", F.Id("F")),
            Call("mk", Lambda("n", Call("abs", Coefficient(N(), F.Id("F"))))))));

    private static Formula SequenceDefinition() => Disp(new Formula.Aligned([
        Equal(Call("P", D(0)), D(1)),
        Seq(Bound("r", Naturals()), Equal(Call("P", Add(R(), D(1))), Step(Call("P", R())))),
        Seq(Bound("n", Naturals()), Equal(Call("a", N()),
            Coefficient(N(), Call("P", Add(N(), D(1))))))
    ]));

    private static Formula UniqueFormula() => Disp(Seq(Bound("B", Series()),
        Implication(Equal(Constant(F.Id("B")), D(1)),
            Implication(Equation(F.Id("B")), Equal(F.Id("B"), A())))));

    private static Formula LucasFormula() => Disp(Seq(Bound("r", Naturals()),
        Conjunction(
            Equal(Mod(QChoose(Add(Mul(D(4), R()), D(1)))), Mod(Call("choose", Add(Mul(D(4), R()), D(1)), R()))),
            Conjunction(
                Equal(Mod(QChoose(Add(Mul(D(4), R()), D(3)))), D(0)),
                Equal(Mod(QChoose(Mul(D(2), R()))), Conditional(Equal(R(), D(0)), D(1), D(0)))))));

    private static Formula ReductionFormula() => Disp(Equal(Reduce(A()),
        Call("mk", Lambda("n", Conditional(Equal(N(), D(0)), D(1),
            Call("zmodCast", HChoose(N()), Call("ZMod", D(2))))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(0), Sp, Lt, Sp, N()),
            Equal(Mod(Call("a", N())), Mod(Call("ofNat", HChoose(N())))))));
}
