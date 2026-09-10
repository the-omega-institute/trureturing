using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SelfReferentialInverseSeriesParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/SelfReferentialInverseSeriesParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a393170");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A393170 are odd exactly at powers of two.",
        H("Self-Referential Inverse Series Parity"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A393170 entry defines an integer "
                + "series A by requiring coefficient n of the reciprocal of A-nX to "
                + "vanish at every positive n, fixes a(0)=1, and states the parity conjecture.")),
            Paragraph(Text("PowerSeries(R) is the formal power-series ring over R, X is "
                + "its indeterminate, coeff(n,F) is the degree-n coefficient, and "
                + "constantCoeff(F) is the constant coefficient. The expression "
                + "invOfUnit(F,1) is Mathlib's inverse for a series whose constant "
                + "coefficient is one. The operation map(intCast,ZMod(2)) reduces "
                + "integer coefficients modulo two. All indices and exponents are natural numbers.")),
            Node("exists_solution", "Existence of a normalized source series",
                ExistsSolutionFormula(),
                "Set a(0)=1. At each positive n, form the prefix containing the already "
                + "chosen coefficients below n and choose a(n) to be coefficient n of "
                + "the inverse of that prefix minus nX. The inverse recurrence depends "
                + "only on coefficients through degree n, and adding a(n)X^n changes its "
                + "degree-n coefficient by minus a(n). Strong recursion therefore builds "
                + "an integer series satisfying all the required equations."),
            Node("generating_equation", "Parity separation", GeneratingEquationFormula(),
                "Put F=map(intCast,A), B=1/F, and C=1/(F+X). The even-index source "
                + "conditions make the positive even coefficients of B vanish, while "
                + "the odd-index conditions make the odd coefficients of C vanish. "
                + "Thus B=1+X*U(X^2) and C=V(X^2). From C*(1+X*B)=B, comparison "
                + "of odd coefficients gives V=U and hence B=1+X*C. Multiplication "
                + "by F*(F+X), followed by characteristic-two cancellation, gives F^2+F=X."),
            Node("generating_unique", "The normalized quadratic root is unique",
                GeneratingUniqueFormula(),
                "If F and the constant-one Artin series S satisfy the same quadratic "
                + "equation, then (1+F+S)*(F-S)=0. The first factor has unit constant "
                + "coefficient, so cancellation gives F=S."),
            Node("mod_two_identity", "Identification with the Artin series",
                ModTwoIdentityFormula(),
                "The parity-separation equation and uniqueness identify the reduction "
                + "of every normalized source solution with the Artin series."),
            Node("unit_constant_support", "Support of the constant-one root",
                UnitSupportFormula(),
                "The uniqueness theorem identifies any constant-one root with the "
                + "Artin series. Its coefficient at zero and at each power of two is one, "
                + "and every other coefficient is zero."),
            Node("a393170_conjecture", "The A393170 parity conjecture", ConjectureFormula(),
                "At a positive index, reduction modulo two sends the integer coefficient "
                + "to one exactly when it is odd. The reduction identity and the support "
                + "of the constant-one root therefore leave precisely the powers of two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("a393170-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModTwo() => Call("ZMod", D(2));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula A() => F.Id("A");
    private static Formula Root() => F.Id("F");
    private static Formula X() => F.Id("X");
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
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Reduced(Formula value) =>
        Call("map", Call("intCast", ModTwo()), value);
    private static Formula InverseAt(Formula series, Formula n) =>
        Call("invOfUnit", Subtract(series, Mul(Call("C", Call("castZ", n)), X())), D(1));
    private static Formula Quadratic(Formula value) =>
        Equal(Add(Power(value, D(2)), value), X());
    private static Formula IsPowerTwo(Formula n) => Seq(
        Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
        Equal(n, Power(D(2), F.Id("k"))));
    private static Formula SourceHypothesis(Formula series) => Seq(
        Bound("n", Naturals()), Implication(Seq(D(0), Sp, Lt, Sp, N()),
            Equal(Call("coeff", N(), InverseAt(series, N())), D(0))));
    private static Formula NormalizedSource(Formula series) => And(
        Equal(Call("constantCoeff", series), D(1)), SourceHypothesis(series));

    private static Formula ExistsSolutionFormula() => Disp(Seq(
        Exists, Sp, F.Id("A"), Colon, Sp, Series(Integers()), Comma, Sp,
        NormalizedSource(A())));

    private static Formula GeneratingEquationFormula() => Disp(Seq(
        Bound("A", Series(Integers())),
        Implication(NormalizedSource(A()), Quadratic(Reduced(A())))));

    private static Formula GeneratingUniqueFormula() => Disp(Seq(
        Bound("F", Series(ModTwo())),
        Implication(Equal(Call("constantCoeff", Root()), D(1)),
            Implication(Quadratic(Root()), Equal(Root(), Named("artinSeries"))))));

    private static Formula ModTwoIdentityFormula() => Disp(Seq(
        Bound("A", Series(Integers())),
        Implication(NormalizedSource(A()),
            Equal(Reduced(A()), Named("artinSeries")))));

    private static Formula UnitSupportFormula() => Disp(Seq(
        Bound("F", Series(ModTwo())),
        Implication(Equal(Call("constantCoeff", Root()), D(1)),
            Implication(Quadratic(Root()), Seq(
                Bound("n", Naturals()),
                Parenthesized(Seq(
                    Equal(Call("coeff", N(), Root()), D(1)), Sp, Iff, Sp,
                    Parenthesized(Seq(Equal(N(), D(0)), Sp, Lor, Sp, IsPowerTwo(N()))))))))));

    private static Formula ConjectureFormula() => Disp(Seq(
        Bound("A", Series(Integers())),
        Implication(NormalizedSource(A()), Seq(
            Bound("n", Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, N()),
                Parenthesized(Seq(Call("Odd", Call("coeff", N(), A())), Sp, Iff, Sp,
                    Parenthesized(IsPowerTwo(N())))))))));
}
