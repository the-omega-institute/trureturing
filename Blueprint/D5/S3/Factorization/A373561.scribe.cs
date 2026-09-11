using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class A373561Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/A373561.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2024a373561");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisor condition sorts the summands into classes rather than restricting "
        + "them, leaving a square-sum identity.",
        H("Divisor-Bucketed Quadruple Sum"),
        Blocks(
            Paragraph(Text(
                "Indices run over the interval from one to n, which includes both "
                + "endpoints. The summand is an integer and may be zero or negative; the "
                + "divisor is taken of its absolute value. Sums are over finite index sets, "
                + "so no convergence question arises.")),
            Node("f", "The summand", SummandFormula(),
                "Two positive squares against one negative square. The value is an integer "
                + "rather than a natural number precisely so that the negative case is not "
                + "silently truncated.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gcd_buckets_eq_sum", "The condition sorts rather than restricts",
                BucketFormula(),
                "For a positive n the divisor of any summand with n lies between one and n, "
                + "so each triple falls into exactly one class of the outer index. Summing "
                + "over all classes therefore returns the threefold sum unchanged. A "
                + "vanishing summand is not an exception: the divisor of zero with n is n, "
                + "which is still a legitimate class. At n equal to zero every index set is "
                + "empty and both sides vanish.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("triple_sum_eq", "The threefold sum", TripleFormula(),
                "Each of the two positive squares contributes a full square sum scaled by "
                + "the square of the interval length, and the negative square cancels one of "
                + "them, leaving that square times a single square sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a373561_core", "The two layers composed", CoreFormula(),
                "Nothing new is proved here; it records the composition that the closed "
                + "form is then read off from.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("a373561", "The conjecture", MainFormula(),
                "The printed form divides by six, and division on the integers truncates, "
                + "so the final step multiplies through by six instead and appeals to the "
                + "standard square-sum formula. The statement holds for every natural n, "
                + "the empty case included.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a373561-gcd-bucketed-quadruple-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a373561-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SummandFormula() => Disp(Seq(
        Call("f", X(), Y(), Z()), Sp, Eq, Sp,
        Subtract(Add(Sq(X()), Sq(Y())), Sq(Z()))));

    private static Formula BucketFormula() => Universal(Seq(
        SumIn(K()), SumIn(Z()), SumIn(Y()), SumIn(X()),
        Bracket(Seq(Call("gcd", Abs(Call("f", X(), Y(), Z())), N()), Sp, Eq, Sp, K())),
        Sp, Call("f", X(), Y(), Z()), Sp, Eq, Sp,
        SumIn(Z()), SumIn(Y()), SumIn(X()), Call("f", X(), Y(), Z())));

    private static Formula TripleFormula() => Universal(Seq(
        SumIn(Z()), SumIn(Y()), SumIn(X()), Call("f", X(), Y(), Z()), Sp, Eq, Sp,
        Mul(Sq(N()), Seq(SumIn(X()), Sq(X())))));

    private static Formula CoreFormula() => Universal(Seq(
        SumIn(K()), SumIn(Z()), SumIn(Y()), SumIn(X()),
        Bracket(Seq(Call("gcd", Abs(Call("f", X(), Y(), Z())), N()), Sp, Eq, Sp, K())),
        Sp, Call("f", X(), Y(), Z()), Sp, Eq, Sp,
        Mul(Sq(N()), Seq(SumIn(X()), Sq(X())))));

    private static Formula MainFormula() => Universal(Seq(
        SumIn(K()), SumIn(Z()), SumIn(Y()), SumIn(X()),
        Bracket(Seq(Call("gcd", Abs(Call("f", X(), Y(), Z())), N()), Sp, Eq, Sp, K())),
        Sp, Call("f", X(), Y(), Z()), Sp, Eq, Sp,
        Frac, Grp(Mul(Cube(N()), Mul(Grp(Add(N(), D(1))), Grp(Add(Mul(D(2), N()), D(1)))))),
        Grp(D(6))));

    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula SumIn(Formula v) => Seq(
        new Formula.Subscript(F.Sum, Seq(v, Sp, InMacro, Sp, Call("Icc", D(1), N()))), Sp);
    private static Formula Bracket(Formula body) => Seq(OpenBracket, body, CloseBracket);
    private static Formula Abs(Formula v) => Seq(Lvert, v, Rvert);
    private static Formula Sq(Formula v) => Seq(Grp(v), Caret, Grp(D(2)));
    private static Formula Cube(Formula v) => Seq(Grp(v), Caret, Grp(D(3)));
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula X() => F.Id("x");
    private static Formula Y() => F.Id("y");
    private static Formula Z() => F.Id("z");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
