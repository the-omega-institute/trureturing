using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class AlternatingGcdSumPillaiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/AlternatingGcdSumPillai.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/bala2024a344598");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's alternating gcd sum equals the floor-square totient sequence A344598.",
        H("Bala's Alternating Gcd Sum"),
        Blocks(
            Paragraph(Text("The conjecture recorded in bala2024a344598 identifies OEIS "
                + "A344598 with an alternating gcd sum at every positive index. The note "
                + "also records the separate attribution of the divisor-sum formulas to "
                + "Daniel Weber. The identity follows by relating both sums to Pillai's function.")),
            Paragraph(Text("All indices are natural numbers. The functions a and pillai "
                + "take natural-number values; altGcdSum takes integer values. The symbol "
                + "div denotes natural-number integer division. All subtraction in the "
                + "definition of a is truncated natural subtraction. The function toInt "
                + "is the canonical embedding of a natural number into the integers. "
                + "Subtraction in the subsequent theorem formulas is integer subtraction.")),
            Node("a", "The floor-square totient sequence", AFormula(),
                "This is the defining sum of A344598. The function totient is Euler's "
                + "totient function, and Icc(1,n) includes both endpoints.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pillai", "Pillai's function", Universal(Equal(P(N()),
                SumTo(N(), Call("gcd", K(), N())))),
                "Each positive integer k at most n contributes gcd(k,n).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("altGcdSum", "The alternating half-sum", Universal(Equal(S(N()),
                SumTo(Mul(D(2), N()), Mul(Power(Parenthesized(Seq(Minus, D(1))), K()),
                    ToInt(Call("gcd", K(), Mul(D(4), N()))))))),
                "The alternating signs and the gcd values are multiplied and summed "
                + "in the integers over k from one through 2n.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a_eq_two_pillai_sub", "The totient sum in terms of Pillai's function",
                Positive(Equal(ToInt(Call("a", N())),
                    Subtract(Mul(D(2), ToInt(P(N()))), ToInt(N())))),
                "The quotient square changes only when k divides n; its increment is "
                + "2 div(n,k)-1. Grouping the gcd sum by its gcd fibres uses Mathlib's "
                + "totient_div_of_dvd. Reindexing complementary divisors gives the "
                + "totient-weighted quotient sum, and sum_totient supplies the subtracted n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("pillai_four_mul", "The doubling identity", Universal(Equal(
                Add(P(Mul(D(4), N())), Mul(D(4), P(N()))),
                Mul(D(4), P(Mul(D(2), N()))))),
                "This equality is in the natural numbers and includes n=0. Even "
                + "indices contribute twice the smaller gcd sum. For odd indices, "
                + "coprimality with two removes the extra factor two from the modulus. "
                + "Splitting the odd-index sum into two blocks of length n gives "
                + "two equal sums, which yields the displayed identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("altGcdSum_eq", "Reflection and endpoint terms", Positive(Equal(
                Add(Mul(D(2), S(N())), Mul(D(2), ToInt(N()))),
                Subtract(Mul(D(4), ToInt(P(Mul(D(2), N())))),
                    ToInt(P(Mul(D(4), N())))))),
                "Reflection k to 4n-k preserves the sign and gcd. In the half-open "
                + "range from zero to 2n, replacing zero by 2n changes the sum by "
                + "2n, since the endpoint values are 4n and 2n. The reflected upper "
                + "half equals altGcdSum(n). Splitting the full sum by parity gives "
                + "4 pillai(2n)-pillai(4n), including exactly the displayed endpoint term.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture", "Bala's conjectured formula", Positive(Equal(
                ToInt(Call("a", N())), S(N()))),
                "The doubling identity and reflection identity imply "
                + "altGcdSum(n)=2 pillai(n)-n. The totient identity gives the same "
                + "integer for a(n), proving the conjectured formula for every positive n.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a344598-alternating-gcd-sum-pillai"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("alternating-gcd-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula AFormula() => Universal(Equal(Call("a", N()),
        SumTo(N(), Mul(Call("totient", K()), Parenthesized(Subtract(
            Power(Call("div", N(), K()), D(2)),
            Power(Call("div", Parenthesized(Subtract(N(), D(1))), K()), D(2))))))));

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula P(Formula n) => Call("pillai", n);
    private static Formula S(Formula n) => Call("altGcdSum", n);
    private static Formula ToInt(Formula value) => Call("toInt", value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula Positive(Formula body) => Universal(Seq(
        D(1), Sp, Le, Sp, N(), Sp, Implies, Sp, body));
    private static Formula SumTo(Formula upper, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(K(), Sp, InMacro, Sp, Call("Icc", D(1), upper))),
        Sp, Parenthesized(body));
}
