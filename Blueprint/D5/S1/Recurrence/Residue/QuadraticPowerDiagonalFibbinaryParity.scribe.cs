using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class QuadraticPowerDiagonalFibbinaryParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/QuadraticPowerDiagonalFibbinaryParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a397244");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A397244 are odd exactly at twice a Fibbinary number plus one.",
        H("Quadratic Power Diagonals and Fibbinary Parity"),
        Blocks(
            Paragraph(Text("The NAME and conjecture are quoted in hanna2026a397244. "
                + "Write A for generatingSeries, the integer series with coefficient function a. "
                + "The strict-prefix recurrence starts with a(0)=a(1)=1 and uses only "
                + "coefficients below n to define a(n). The formalization uses the NAME "
                + "and that recurrence; the source note records the formula erratum.")),
            Paragraph(Text("Write S for A.map(Int.castRingHom(ZMod(2))) and T for "
                + "D5.S1.Recurrence.Parity.StripThreeTernaryCatalanParity.generatingSeries.map"
                + "(Int.castRingHom(ZMod(2))). Thus S and T are series over ZMod(2), "
                + "while A and the universally quantified B are series over the integers. "
                + "All indices have type natural number. The notation intCast(n) is the "
                + "cast (n : integers), coeff(n,F) extracts the coefficient at n, and "
                + "expand(2,T) substitutes X^2 for X; its proof that 2 is nonzero is implicit. "
                + "X is the indeterminate. Fibbinary is the imported predicate "
                + "D5.S1.Recurrence.Parity.FibbinarySquareSubstitutionParity.Fibbinary: "
                + "f bitwise-and (f shifted right by one) equals zero.")),
            Node("a_two", "The second coefficient", Disp(Equal(Call("a", D(2)), D(6))),
                "The prefix is 1+X. The recurrence gives 3*choose(5,2)-4*choose(4,2)=6."),
            Node("generating_equation", "The exact diagonal equations", EquationFormula(),
                "The frozen diagonal multiplier compares each power with its strict prefix. "
                + "The recurrence cancels the resulting coefficient difference and gives "
                + "the displayed relation for every n greater than one."),
            Node("generating_unique", "Uniqueness over the integers", UniqueFormula(),
                "The private equation_unique proves uniqueness over any commutative ring "
                + "by strong induction and the frozen diagonal multiplier. Specializing "
                + "to the integers gives B=A with both initial coefficients and all "
                + "diagonal equations present as hypotheses."),
            Node("mod_two_cubic", "The cubic equation modulo two", CubicFormula(),
                "The private even_power_diagonal proves coeff(n,F^(2*n))=0 for every "
                + "series over ZMod(2) and every positive n by Frobenius descent. "
                + "The private cubic_diagonal uses it to turn the frozen candidate's "
                + "cubic equation into A397244's diagonal relations. The general "
                + "equation_unique then identifies S with the candidate."),
            Node("mod_two_identity", "The ternary-series reduction", ReductionFormula(),
                "The proved equality of reductions transports the frozen candidate's "
                + "identity S=1+X*expand(2,T). This is equality modulo two, not equality "
                + "of the two integer sequences."),
            Node("hanna_conjecture_a397244", "Hanna's A397244 conjecture", ConjectureFormula(),
                "Coefficient equality of the reductions transports Odd(a(n)) to the "
                + "frozen AbsoluteReciprocalSquareFibbinaryParity.hanna_conjecture. "
                + "The new Frobenius diagonal lemma remains on the live path through "
                + "reduction_eq_candidate; the integer sequences are not identified.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397244-quadratic-power-diagonal-fibbinary-parity"),
                    ResolutionKind.Proved))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Residue/AbsoluteReciprocalSquareFibbinaryParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Parity/StripThreeTernaryCatalanParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity"))
        ]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397244-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula S() => F.Id("S");
    private static Formula T() => F.Id("T");
    private static Formula N() => F.Id("n");
    private static Formula X() => F.Id("X");
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
        Mul(Parenthesized(Mul(D(2), Call("intCast", N()))),
            Coefficient(N(), Power(value, Mul(D(2), N())))),
        Mul(Parenthesized(Subtract(Mul(D(2), Call("intCast", N())), D(1))),
            Coefficient(N(), Power(value, Add(Mul(D(2), N()), D(1))))));
    private static Formula Relations(Formula value) => Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Diagonal(value)));

    private static Formula EquationFormula() => Disp(
        Conjunction(Equal(Coefficient(D(0), A()), D(1)),
            Conjunction(Equal(Coefficient(D(1), A()), D(1)), Relations(A()))));

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Relations(b), Equal(b, A()))))));
    }

    private static Formula CubicFormula() => Disp(Equal(Power(S(), D(3)),
        Add(Power(S(), D(2)), X())));

    private static Formula ReductionFormula() => Disp(Equal(S(),
        Add(D(1), Mul(X(), Call("expand", D(2), T())))));

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
