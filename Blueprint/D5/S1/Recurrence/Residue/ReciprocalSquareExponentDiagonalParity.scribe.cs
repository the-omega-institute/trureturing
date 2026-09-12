using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ReciprocalSquareExponentDiagonalParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/ReciprocalSquareExponentDiagonalParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a397356");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A397356 are odd exactly when their index plus one is a power of two.",
        H("Reciprocal Square-Exponent Diagonals and Catalan Parity"),
        Blocks(
            Paragraph(Text("OEIS A397356 has two conjectures. Only the parity conjecture "
                + "is proved here; the second conjecture, on divisibility by three, remains open. "
                + "The defining equation and both conjectures are quoted in hanna2026a397356.")),
            Paragraph(Text("Write R for reciprocalSeries and G for generatingSeries, both "
                + "power series over the integers, and a(n)=coeff(n,G). The coefficient "
                + "function r defines R=PowerSeries.mk(r), and G=PowerSeries.invOfUnit(R,1). "
                + "Write v for one plus the reduction modulo two of "
                + "D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries. "
                + "This series over ZMod(2) satisfies v^2=v+X, where X is the indeterminate. "
                + "Write S for R.map(Int.castRingHom(ZMod(2))). The notation coeff(n,F) "
                + "extracts the coefficient of X^n in F. All indices and exponents are "
                + "natural numbers, and subtraction in an exponent is truncated natural subtraction.")),
            Node("v_diagonal", "The binary Catalan diagonal", DiagonalFormula(),
                "The powers v^(n^2) and v^(n^2-1) have equal coefficients at n for n>1. "
                + "The residual diagonal vanishes after splitting on the parity of n. "
                + "A coefficient at an odd degree of a square vanishes in the even case; square "
                + "extraction in the odd case reduces the residual to a Frobenius diagonal."),
            Node("generating_equation", "The defining inverse pair", EquationFormula(),
                "R and G are inverse, and a(0)=a(1)=1. The strict-prefix recurrence for r "
                + "cancels the difference of the square-exponent diagonals of R for n>1. "
                + "Since R is the reciprocal of G, this is the entry's defining relation "
                + "and makes a its coefficient sequence."),
            Node("generating_unique", "Uniqueness of the inverse pair", UniqueFormula(),
                "Any integer series B with constant coefficient 1, linear coefficient -1, "
                + "and the same square-exponent diagonal relation equals R. Strong induction "
                + "compares coefficients using the diagonal multiplier. If B*A=1 as well, "
                + "uniqueness of the inverse gives A=G."),
            Node("mod_two_identity", "The reciprocal modulo two", ReductionFormula(),
                "Reduction of R modulo two equals v. The initial coefficients and the "
                + "diagonal relations agree, so uniqueness over ZMod(2) identifies them."),
            Node("hanna_conjecture_a397356", "Hanna's A397356 parity conjecture", ConjectureFormula(),
                "The identity S=v identifies the reduction of G with the unit inverse "
                + "of v. Multiplication of that inverse by X gives the binary Catalan "
                + "series. Its coefficient description therefore yields Odd(a(n)) exactly "
                + "when n+1 is a power of two, including n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397356-reciprocal-square-exponent-diagonal-parity"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd"))
        ]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397356-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula S() => F.Id("S");
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Star, Sp, right);
    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Parenthesized(value), Caret, Grp(exponent));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula index, Formula value) => Call("coeff", index, value);
    private static Formula Diagonal(Formula value) => Equal(
        Coefficient(N(), Power(value, Power(N(), D(2)))),
        Coefficient(N(), Power(value, Subtract(Power(N(), D(2)), D(1)))));
    private static Formula Relations(Formula value) => Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Diagonal(value)));

    private static Formula DiagonalFormula() => Disp(Relations(F.Id("v")));

    private static Formula EquationFormula() => Disp(
        Conjunction(Equal(Mul(F.Id("R"), F.Id("G")), D(1)),
            Conjunction(Equal(Call("a", D(0)), D(1)),
                Conjunction(Equal(Call("a", D(1)), D(1)), Relations(F.Id("R"))))));

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()), Bound("A", Series()),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equal(Coefficient(D(1), b), Seq(Minus, D(1))),
                    Implication(Relations(b),
                        Implication(Equal(Mul(b, A()), D(1)),
                            Conjunction(Equal(b, F.Id("R")), Equal(A(), F.Id("G")))))))));
    }

    private static Formula ReductionFormula() => Disp(Equal(S(), F.Id("v")));

    private static Formula ConjectureFormula()
    {
        var k = F.Id("k");
        return Disp(Seq(Bound("n", Naturals()),
            Call("Odd", Call("a", N())), Sp, Iff, Sp,
            Parenthesized(Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
                Equal(Add(N(), D(1)), Power(D(2), k))))));
    }
}
