using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThetaGaussianPairingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Gaussian tails control the higher modes and pairing errors. Cancellation " +
        "between paired translated terms yields a positive sine-shaped force lower bound.",
        H("Gaussian tails and translated pairing"), Blocks([.. Section0.Entries(), .. Section1.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("gaussianTail", "Normalized tail", Definition(),
                "The index k enumerates the positive modes n equal to k plus two. " +
                "Subtracting one in the exponent normalizes by the first Gaussian mode.",
                true),
            Entry("gaussian_tail_bound", "Uniform geometric bound", Bound(),
                "For n at least two, n squared is at most four to the power n minus one, " +
                "and n squared minus one is at least three times n minus one. " +
                "Thus the summands are bounded by successive positive powers of " +
                "r equal to four exp of negative three pi v. A finite Taylor bound gives " +
                "exp of three halves greater than four. For v at least one half this " +
                "implies r less than one sixteenth, and the geometric sum is less " +
                "than one fifteenth."),
            Entry("gaussian_tail_scaled_bound", "Exponential margin", Scaled(),
                "If s lies in the interval zero to pi over six and v is at least three " +
                "divided by four s, the scaled exponent is at most negative twelve " +
                "times n minus one. The identity three n squared minus four at least " +
                "eight times n minus one gives this comparison. The geometric ratio " +
                "four exp of negative twelve is less than one forty-thousandth, " +
                "since the Taylor lower bound exp of three greater than twenty " +
                "implies exp of twelve greater than one hundred sixty thousand. " +
                "Summing gives the strict bound one over thirty-nine thousand " +
                "nine hundred ninety-nine. The estimates are a derivation for the " +
                "one-dimensional theta comparison underlying Montgomery's planar minimum."),
            Entry("gaussianPairTail", "Gaussian pairing error", PairDefinition(),
                "For positive integers n, the normalized pairing error is four a " +
                "times the sum of (n minus one quarter) squared times " +
                "exp of negative a times n squared minus n over two.", true),
            Entry("gaussian_pair_tail_bound", "Pairing tail bound", PairBound(),
                "The inequality one plus u at most exp u bounds a exp of negative " +
                "a d by six exp of negative six d whenever a is at least six " +
                "and d is at least one half. The n equal to one term is bounded " +
                "by twenty-seven halves times exp of negative three. For n at least two the exponent " +
                "is at most negative nine n; a geometric series bounds the " +
                "remaining sum by ninety-six times exp of negative eighteen divided by one minus four " +
                "times exp of negative nine. This explicit total is strictly less " +
                "than seven tenths, and therefore less than three quarters.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-tail-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaGaussianPairing." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula ExpF(Formula a) => Call("exp", a);
    private static Formula Tail(Formula v) => Call("gaussianTail", v);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Term(Formula v) => Mul(Sq(Add(V("k"), D(2))),
        ExpF(new Formula.Negate(Mul(Mul(Pi, v), Sub(Sq(Add(V("k"), D(2))), D(1))))));
    private static Formula Ratio => Mul(D(4),
        ExpF(new Formula.Negate(Mul(Mul(D(3), Pi), V("v")))));
    private static Formula Definition() => All("v", R, Equal(Tail(V("v")),
        Call("tsum", Lam("k", N, Term(V("v"))))));
    private static Formula Bound() => All("v", R, Imp(Le(Div(D(1), D(2)), V("v")),
        And(Call("Summable", Lam("k", N, Term(V("v")))),
            And(Le(Tail(V("v")), Div(Ratio, Sub(D(1), Ratio))),
                Lt(Tail(V("v")), Div(D(1), D(1, 5)))))));
    private static Formula Scaled() => All("s", R, All("v", R,
        Imp(Lt(D(0), V("s")), Imp(Le(V("s"), Div(Pi, D(6))),
            Imp(Le(Div(D(3), Mul(D(4), V("s"))), V("v")),
                Lt(Mul(ExpF(Div(Pi, Mul(D(4), V("s")))), Tail(V("v"))),
                    Div(D(1), D(3, 9, 9, 9, 9))))))));
    private static Formula PairTerm() => Mul(Mul(Mul(D(4), V("a")),
        Sq(Add(V("k"), Div(D(3), D(4))))),
        ExpF(new Formula.Negate(Mul(V("a"),
            Sub(Sq(Add(V("k"), D(1))), Div(Add(V("k"), D(1)), D(2)))))));
    private static Formula PairDefinition() => All("a", R,
        Equal(Call("gaussianPairTail", V("a")), Call("tsum", Lam("k", N, PairTerm()))));
    private static Formula PairBound() => All("a", R, Imp(Le(D(6), V("a")),
        And(Call("Summable", Lam("k", N, PairTerm())),
            Le(Call("gaussianPairTail", V("a")), Add(
                Mul(Div(D(2, 7), D(2)), ExpF(new Formula.Negate(D(3)))),
                Div(Mul(D(9, 6), ExpF(new Formula.Negate(D(1, 8)))),
                    Sub(D(1), Mul(D(4), ExpF(new Formula.Negate(D(9)))))))))));

    }

    private static class Section1
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("gaussianForce", "Periodized Gaussian force", Definition(),
                "The signed sum records the derivative of the periodized Gaussian " +
                "apart from its positive normalization. All integer translates are retained.",
                true),
            Entry("summable_gaussian_force", "Absolute convergence", Summability(),
                "The translated first Gaussian moment is the integer Hurwitz kernel moment of order " +
                "one, with shift negative b and temperature a divided by pi. Its summability directly " +
                "gives absolute convergence."),
            Entry("gaussian_force_lower", "Closed half-period bound", Lower(),
                "For b at most one quarter, pair positive and negative integers. " +
                "The negative derivative of u exp of negative a u squared decreases " +
                "for u at least three quarters when a is at least six. The mean value " +
                "theorem bounds each pair by the corresponding normalized Gaussian " +
                "pairing-tail summand. The seven-tenths tail bound leaves at least " +
                "three tenths of the central term. For b between one quarter and " +
                "one half, pair around one half. All pairs beyond the first are " +
                "nonnegative. With delta equal to one half minus b, the first pair " +
                "is at least delta divided by two times exp of negative a over four. " +
                "This follows from one minus exp of negative four delta at least " +
                "two delta. Finally sin of two pi b is bounded by two pi times " +
                "the distance to the nearest endpoint. The result holds for every " +
                "a at least six and every b in the closed half-period.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-pair-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaGaussianPairing." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula ExpF(Formula a) => Call("exp", a);
    private static Formula Force(Formula a, Formula b) => Call("gaussianForce", a, b);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Term() => Mul(Sub(V("b"), V("m")),
        ExpF(NegF(Mul(V("a"), Sq(Sub(V("b"), V("m")))))));
    private static Formula Definition() => All("a", R, All("b", R,
        Equal(Force(V("a"), V("b")), Call("tsum", Lam("m", Z, Term())))));
    private static Formula Summability() => All("a", R, Imp(Lt(D(0), V("a")),
        All("b", R, Call("Summable", Lam("m", Z, Term())))));
    private static Formula Lower() => All("a", R, All("b", R,
        Imp(Le(D(6), V("a")), Imp(Le(D(0), V("b")),
            Imp(Le(V("b"), Div(D(1), D(2))),
                Le(Mul(Mul(Div(D(3), Mul(D(2, 0), Pi)),
                    ExpF(NegF(Div(V("a"), D(4))))),
                    Call("sin", Mul(Mul(D(2), Pi), V("b")))),
                    Force(V("a"), V("b"))))))));
    }
}
