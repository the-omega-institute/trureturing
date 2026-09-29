using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class ForcedCoreNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ExponentExchange/ForcedCoreNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constrained divisor-sum maximum has an exact ordered prime-prefix representative.",
        H("Mandatory-Core Prime Prefix Normalization"),
        Blocks(
            Paragraph(Text(
                "Let q(i) be the i-th prime strictly above one, so q(0)=2. "
                + "S(i,t) is RoughPrimeSuffixBellman.suffixNumber 1 i t, and W(i,t) is "
                + "RoughPrimeSuffixBellman.suffixWeight 1 i t. Ordered(h,t) is the supplier's "
                + "positive, nonincreasing list predicate with first exponent at most h. "
                + "The empty list is ordered and S(i,[]) = W(i,[]) = 1. The symbol v(n,p) "
                + "means Nat.factorization n at p; Z(n) means the real ratio "
                + "ArithmeticFunction.sigma 1 n divided by n. c(B) means rootCap 1 B. "
                + "The input ell is any finite list of natural exponents satisfying "
                + "Ordered(headD(ell,0),ell); this is exactly a positive nonincreasing "
                + "mandatory profile, including the empty profile.")),
            Describe.Lean(
                DescribeId.Create("forced-core-normalization"),
                DeclarationHandle.Create(Prefix + "forced_core_normalization"),
                H("Attainment in the mandatory-divisor fiber"),
                StatementSource.FromAuthor(CompleteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every such ell and every natural budget B, M is the exact "
                        + "consecutive-prime core S(0,ell). The first equivalence states "
                        + "that B<M exactly when there is no positive multiple of M in [1,B]. "
                        + "If M<=B, the existential witness n is an actual constrained "
                        + "maximizer. Its total valuations are antitone across every pair "
                        + "of distinct primes p<q. The list t represents that same integer, "
                        + "has positive nonincreasing entries, and is bounded at the head "
                        + "by c(B). Its suffix weight equals the actual sigma ratio. The "
                        + "last universal clause compares n with every positive multiple "
                        + "of M within the budget.")),
                    Paragraph(Text(
                        "The proof selects a maximum from the finite constrained fiber. "
                        + "A strict valuation inversion would admit IntegerSwap's smaller "
                        + "integer with a larger normalized divisor sum. Factorization of "
                        + "the mandatory list and its antitone profile show that this swap "
                        + "preserves divisibility by the whole M, including when the smaller "
                        + "valuation is zero. This contradicts maximality. The supplier's "
                        + "prime enumeration and factorization product then reconstruct "
                        + "the same n from its positive valuation prefix; its sigma identity "
                        + "gives the exact W value. No coprimality or multiplicative "
                        + "identity between M and a quotient of n is assumed.")),
                    Paragraph(Text(
                        "This theorem covers B=0, B=M, M=1, and the empty exponent list. "
                        + "It proves the normalization assertion of source theorem 91.1. "
                        + "It supplies no forced-suffix Bellman recurrence or 91.2 pruning "
                        + "claim."))),
                DescribeRole.Theorem))));

    private static Formula I(string value) => F.Id(value);
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(I(name), [.. args]);
    private static Formula N => Seq(Mathbb, Grp(I("N")));
    private static Formula Lists => App("List", N);
    private static Formula Core => App("S", D(0), I("ell"));
    private static Formula Suffix => App("S", D(0), I("t"));
    private static Formula Weight => App("W", D(0), I("t"));
    private static Formula Dvd(Formula a, Formula b) => App("dvd", a, b);
    private static Formula Z(Formula n) => App("Z", n);
    private static Formula Val(Formula n, Formula p) => App("v", n, p);

    private static Formula CompleteFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, I("ell"), Colon, Lists, Comma, Sp,
            App("Ordered", App("headD", I("ell"), D(0)), I("ell")), Rightarrow,
            Forall, Sp, I("B"), Colon, N, Comma),
        Seq(I("M"), Eq, Core, Comma, Sp, OpenBracket),
        Seq(I("B"), Lt, I("M"), Leftrightarrow, Neg, Exists, Sp, I("n"), Colon, N,
            Comma, Sp, D(1), Le, I("n"), Land, I("n"), Le, I("B"), Land,
            Dvd(I("M"), I("n"))),
        Seq(Land, Open, I("M"), Le, I("B"), Rightarrow, Exists, Sp,
            I("n"), Colon, N, Comma, Exists, Sp, I("t"), Colon, Lists, Comma),
        Seq(D(1), Le, I("n"), Land, I("n"), Le, I("B"), Land,
            Dvd(I("M"), I("n"))),
        Seq(Land, Open, Forall, Sp, I("p"), Comma, I("q"), Colon, N, Comma,
            App("Prime", I("p")), Land, App("Prime", I("q")), Land,
            I("p"), Lt, I("q"), Rightarrow, Val(I("n"), I("q")), Le,
            Val(I("n"), I("p")), Close),
        Seq(Land, App("Ordered", App("c", I("B")), I("t")), Land,
            Suffix, Eq, I("n"), Land, Z(I("n")), Eq, Weight),
        Seq(Land, Open, Forall, Sp, I("m"), Colon, N, Comma,
            D(1), Le, I("m"), Land, I("m"), Le, I("B"), Land,
            Dvd(I("M"), I("m")), Rightarrow,
            Z(I("m")), Le, Z(I("n")), Close, Close, CloseBracket)
    ]));
}
