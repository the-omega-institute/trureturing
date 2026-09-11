using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class AbsoluteReciprocalSquareFibbinaryParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a380708");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A380708 are odd exactly at twice a fibbinary number plus one.",
        H("Absolute Reciprocal Squares and Fibbinary Parity"),
        Blocks(
            Paragraph(Text("The equation and conjecture are recorded in hanna2025a380708. "
                + "Write A for generatingSeries. The imported symbol absSeries is "
                + "D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity.absSeries: "
                + "it takes the integer absolute value of each coefficient before squaring. "
                + "The imported predicate Fibbinary is "
                + "D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity.Fibbinary. "
                + "It asserts n bitwise-and (n shifted right by one) equals zero, "
                + "equivalently that no two adjacent binary digits are both one.")),
            Paragraph(Text("Write T for the imported integer series "
                + "D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries. "
                + "The series A, B, T, and the auxiliary approximations P(r) have integer "
                + "coefficients; P(r) denotes the private approximation(r). All indices "
                + "are natural numbers and X is the indeterminate. "
                + "The operator coeff extracts a coefficient, constantCoeff extracts the "
                + "constant coefficient, and mk forms a series from its coefficient function. "
                + "The operator invOfUnit(F,1) is Mathlib's inverse with unit parameter one. "
                + "The operator map acts coefficientwise; intCastRingHom(ZMod(2)) is "
                + "Int.castRingHom(ZMod(2)), and cast2 embeds a natural number into ZMod(2). "
                + "The operator expand(2,F) substitutes X^2 for X, with its nonzero "
                + "parameter proof implicit. The operator choose denotes Nat.choose.")),
            Node("a", "The stabilized coefficient sequence", SequenceFormula(),
                "Inversion with constant coefficient one, coefficientwise absolute value, "
                + "and squaring preserve agreement below a given degree. Multiplication "
                + "by X increases that degree by one. Thus the coefficient at n "
                + "stabilizes by approximation n+1.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The series A has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The exact functional equation",
                Disp(Conjunction(Equal(Constant(A()), D(1)), Equation(A()))),
                "Stabilization establishes the equation in every degree. Its constant "
                + "coefficient is one, so invOfUnit(A,1) is the reciprocal of A."),
            Node("generating_unique", "Uniqueness of the solution", UniqueFormula(),
                "The two fixed-point equations increase coefficient agreement by one "
                + "degree. Induction proves agreement in every degree, hence B=A."),
            Node("mod_two_identity", "Reduction to the ternary series", ReductionFormula(),
                "Absolute values disappear modulo two. If F is the reduction of A "
                + "and U is its reciprocal, then F=1+X*U^2. Multiplication by U gives "
                + "1=U+X*U^3, hence U=1+X*U^3 in characteristic two. The imported "
                + "generating_equation and strip3_mod_two give the same cubic equation "
                + "for the reduction V of T. Factoring the difference gives "
                + "(U-V)*(1-X*(U^2+U*V+V^2))=0. The second factor has constant "
                + "coefficient one and is a unit, so U=V. Frobenius replaces V^2 "
                + "by expand(2,V), proving the displayed identity."),
            Node("choose_three_odd_iff", "Binomial parity and adjacent binary digits",
                ChooseFormula(),
                "The imported choose_three_lucas theorem reduces the binomial "
                + "coefficient at 2r or 4r+1 to that at r, and makes it zero at 4r+3. "
                + "The bitwise definition gives the same three rules for Fibbinary. "
                + "Strong induction, starting with zero, proves the equivalence."),
            Node("hanna_conjecture", "Hanna's A380708 conjecture", ConjectureFormula(),
                "At a positive even index the shifted expansion has coefficient zero. "
                + "At index 2f+1 it has the degree-f coefficient of the reduction of T. "
                + "The imported mod_two_identity identifies this coefficient with "
                + "choose(3f,f) in ZMod(2). The binomial equivalence therefore proves "
                + "exactly the asserted fibbinary support of the odd coefficients.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380708-absolute-reciprocal-square-fibbinary-parity"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity"))
        ]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a380708-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula T() => F.Id("T");
    private static Formula N() => F.Id("n");
    private static Formula X() => F.Id("X");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Constant(Formula value) => Call("constantCoeff", value);
    private static Formula Step(Formula value) => Add(D(1),
        Mul(X(), Power(Call("absSeries", Call("invOfUnit", value, D(1))), D(2))));
    private static Formula Equation(Formula value) => Equal(value, Step(value));
    private static Formula Reduce(Formula value) =>
        Call("map", Call("intCastRingHom", Call("ZMod", D(2))), value);

    private static Formula SequenceFormula()
    {
        var r = F.Id("r");
        return Disp(new Formula.Aligned([
            Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("r", Naturals()), Equal(Call("P", Add(r, D(1))), Step(Call("P", r)))),
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Call("coeff", N(), Call("P", Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Constant(b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula ReductionFormula() => Disp(Equal(Reduce(A()),
        Add(D(1), Mul(X(), Call("expand", D(2), Reduce(T()))))));

    private static Formula ChooseFormula()
    {
        var f = F.Id("f");
        return Disp(Seq(Bound("f", Naturals()),
            Parenthesized(Equal(Call("cast2", Call("choose", Mul(D(3), f), f)), D(1))),
            Sp, Iff, Sp, Call("Fibbinary", f)));
    }

    private static Formula ConjectureFormula()
    {
        var f = F.Id("f");
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, N()),
                Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                    Parenthesized(Seq(Exists, Sp, f, Colon, Sp, Naturals(), Comma, Sp,
                        Conjunction(Call("Fibbinary", f),
                            Equal(N(), Add(Mul(D(2), f), D(1)))))))))));
    }
}
