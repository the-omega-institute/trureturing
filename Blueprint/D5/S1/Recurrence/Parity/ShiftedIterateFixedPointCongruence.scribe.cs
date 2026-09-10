using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class ShiftedIterateFixedPointCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.";
    private static readonly LibraryNoteRef SourceFive =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a378575");
    private static readonly LibraryNoteRef SourceSix =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a378576");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For r and m at least two with m dividing r-1, the shifted compositional fixed point has all positive coefficients equal to one modulo m.",
        H("Shifted Iterate Fixed Point Congruences"),
        Blocks(
            Paragraph(Text("The entries cited in hanna2024a378575 and hanna2024a378576 "
                + "define A(x)=x+x*iterate(A,r)(x) for r=5 and r=6, respectively. "
                + "They conjecture that the positive-index coefficients are one modulo "
                + "four and five. Both follow from the general shifted-iterate theorem below.")),
            Paragraph(Text("All indices and parameters r and m are natural numbers. "
                + "PowerSeries(R) is the formal power-series ring over R, with indeterminate X. "
                + "The imported CompositionalIterateCongruence defines iterate(f,0)=X and "
                + "iterate(f,j+1) by substituting f into iterate(f,j). Its mobius(c) is X "
                + "times the geometric series with coefficients c^n. Their implicit ring "
                + "arguments are displayed explicitly. The operator mk constructs a "
                + "series from its coefficient function. The map operator takes a ring "
                + "homomorphism followed by a series; intCastRingHom is the canonical "
                + "homomorphism from the integers to the indicated ring. Subtraction r-1 "
                + "is natural subtraction. Coefficients a(r,n) and all remainders are "
                + "integers, with the natural modulus coerced to an integer.")),
            Node("a", "The integer coefficient family", CoefficientFormula(),
                "The auxiliary approximation starts at zero and repeatedly applies "
                + "f mapped to X+X*iterate(f,r). Its coefficients below degree d are "
                + "stable after d steps. The displayed diagonal defines a(r,n).",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series family", GeneratingFormula(),
                "For each r, mk uses the integer coefficient function a(r).",
                DescribeRole.Definition),
            Node("generating_equation", "Existence and the defining equation", EquationFormula(),
                "Substitution of zero-constant series preserves agreement below a given "
                + "degree: powers agree there, and higher powers contribute zero. "
                + "Induction extends this to every compositional iterate. Multiplication "
                + "by X improves agreement by one degree. The stabilized diagonal is "
                + "therefore a fixed point. Its constant coefficient is zero, and its "
                + "linear coefficient is one because every iterate has constant coefficient zero."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "Two zero-constant fixed points agree below degree zero. Repeated "
                + "application of the shifted-iterate contraction gives agreement below "
                + "every degree, so the coefficient extensionality theorem identifies them."),
            Node("mod_identity", "The reduced series is geometric", ModIdentityFormula(),
                "Coefficient mapping commutes with substitution, so the reduced integer "
                + "series satisfies the same fixed-point equation over ZMod(m). The "
                + "divisibility hypothesis makes r equal to one in this ring. The imported "
                + "mobius_iterate identity then gives iterate(mobius(1),r)=mobius(1). "
                + "The geometric-series identity gives mobius(1)=X+X*mobius(1). "
                + "The same degree contraction proves uniqueness over ZMod(m), giving "
                + "the displayed equality."),
            Node("shift_iterate_mod", "The general congruence", CongruenceFormula(),
                "Every positive-degree coefficient of mobius(1) is one. Taking a "
                + "coefficient in the reduced-series identity and using the integer-cast "
                + "congruence equivalence gives the integer remainder. Since m is at "
                + "least two, the remainder of one is one."),
            Node("hanna_conjecture_five", "Hanna's A378575 conjecture", InstanceFormula(5, 4),
                "Set r=5 and m=4 in the general theorem. Four divides 5-1, proving "
                + "the conjecture quoted in hanna2024a378575 for every positive index.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceFive),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378575-shifted-iterate-fixed-point-mod-four"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_six", "Hanna's A378576 conjecture", InstanceFormula(6, 5),
                "Set r=6 and m=5 in the general theorem. Five divides 6-1, proving "
                + "the conjecture quoted in hanna2024a378576 for every positive index.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceSix),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378576-shifted-iterate-fixed-point-mod-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("shifted-iterate-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula R() => F.Id("r");
    private static Formula M() => F.Id("m");
    private static Formula N() => F.Id("n");
    private static Formula X() => F.Id("X");
    private static Formula Zmod() => Call("ZMod", M());
    private static Formula Generating() => Call("generatingSeries", R());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula AtLeast(Formula value, byte lower) => Seq(D(lower), Sp, Le, Sp, value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Approx(Formula depth) => Call("approximation", Integers(), R(), depth);
    private static Formula RightSide(Formula ring, Formula series) =>
        Add(X(), Mul(X(), Call("iterate", ring, series, R())));
    private static Formula Equation(Formula ring, Formula series) =>
        Equal(series, RightSide(ring, series));
    private static Formula Divisibility() => Seq(M(), Sp, Mid, Sp, Parenthesized(Subtract(R(), D(1))));
    private static Formula Parameters(Formula conclusion) => Seq(
        Bound("r", Naturals()), Bound("m", Naturals()),
        Implication(AtLeast(R(), 2), Implication(AtLeast(M(), 2),
            Implication(Divisibility(), conclusion))));
    private static Formula Remainder(Formula r, Formula m) =>
        Equal(new Formula.Modulo(Call("a", r, N()), m), D(1));

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Seq(Bound("r", Naturals()), Bound("n", Naturals()),
            Equal(Call("a", R(), N()), Call("coeff", N(), Approx(Add(N(), D(1)))))),
        Seq(Bound("r", Naturals()), Equal(Approx(D(0)), D(0))),
        Seq(Bound("r", Naturals()), Bound("d", Naturals()),
            Equal(Approx(Add(F.Id("d"), D(1))), RightSide(Integers(), Approx(F.Id("d")))))
    ]));

    private static Formula GeneratingFormula() => Disp(Seq(Bound("r", Naturals()),
        Equal(Generating(), Call("mk", Call("a", R())))));

    private static Formula EquationFormula() => Disp(Seq(Bound("r", Naturals()),
        Implication(AtLeast(R(), 2), Parenthesized(Seq(
            Parenthesized(Equal(Call("constantCoeff", Generating()), D(0))), Sp, Land, Sp,
            Parenthesized(Equal(Call("coeff", D(1), Generating()), D(1))), Sp, Land, Sp,
            Parenthesized(Equation(Integers(), Generating())))))));

    private static Formula UniqueFormula() => Disp(Seq(Bound("r", Naturals()),
        Implication(AtLeast(R(), 2), Seq(Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", F.Id("B")), D(0)),
                Implication(Equation(Integers(), F.Id("B")), Equal(F.Id("B"), Generating())))))));

    private static Formula ModIdentityFormula() => Disp(Parameters(
        Equal(Call("map", Call("intCastRingHom", Zmod()), Generating()),
            Call("mobius", Zmod(), D(1)))));

    private static Formula CongruenceFormula() => Disp(Parameters(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), 1), Remainder(R(), M())))));

    private static Formula InstanceFormula(byte r, byte m) => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), 1), Remainder(D(r), D(m)))));
}
