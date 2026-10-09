using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class LateGrowingRatioLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/LateGrowingRatioLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Shah–Kiselev permutation ratio tends to one and exceeds one at every index at least two.",
        H("The Late Growing Ratio Limit"),
        Blocks(
            Paragraph(Text("For each natural index n, Phi consists of permutations of Fin (2n) "
                + "that fix zero and have nonnegative suffix budgets after subtracting n. "
                + "Reversing the remaining tail identifies these permutations with orderings "
                + "of the integer interval from 1-n to n-1 whose prefix sums are nonnegative.")),
            Describe.Lean(
                DescribeId.Create("shah-kiselev-late-growing-ratio-limit"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Convergence from above"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The normalization is (2n-2) factorial. The ratio converges "
                        + "to one as n tends to infinity, and its numerator is strictly larger "
                        + "than this factorial for every n at least two. At n=1 the ratio is one.")),
                    Paragraph(Text("Split a nonnegative zero-sum ordering after its last proper "
                        + "zero prefix. The prefix is nonnegative and the tail has strictly "
                        + "positive nonempty proper prefixes. Each rotation class has at most "
                        + "one such strictly positive ordering, and has at least one ordering "
                        + "with nonnegative prefixes. This compares the two counts with the "
                        + "factorial number of rotation classes.")),
                    Paragraph(Text("Deleting a marked letter from a zero-sum subset determines "
                        + "the deleted letter. Applying this injection both to subsets and to "
                        + "their complements bounds the factorial-weighted contribution of "
                        + "proper zero-sum subsets by a harmonic convolution. Strong induction "
                        + "gives a uniform bound on the normalized counts, and the resulting "
                        + "harmonic error divided by the alphabet size tends to zero.")),
                    Paragraph(Text("Choose a nonnegative ordering of the alphabet with zero "
                        + "removed. Placing zero at its beginning and at its end gives two "
                        + "distinct nonnegative words in the same rotation class. The map "
                        + "from weak words to rotation classes is then not injective, giving "
                        + "the strict inequality whenever n is at least two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shah-kiselev-2026-late-growing-ratio-limit"),
                    ResolutionKind.Proved)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula N => V("n");
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula CastReal(Formula f) => Par(Seq(f, Colon, Sp, Reals));
    private static Formula PhiCard => Call("card", Call("phi", N));
    private static Formula Factorial => Call("factorial", Par(Seq(D(2), Sp, Cdot, Sp,
        N, Sp, Minus, Sp, D(2))));
    private static Formula Ratio => new Formula.Fraction(CastReal(PhiCard), CastReal(Factorial));
    private static Formula Limit => Seq(Qualified("Filter", "Tendsto"), Par(Seq(
        Par(Seq(N, Colon, Sp, Naturals, Sp, Mapsto, Sp, Ratio)), Comma, Sp,
        Qualified("Filter", "atTop"), Comma, Sp, Call("nhds", CastReal(D(1))))));
    private static Formula Strictness => Seq(Forall, Sp, N, Colon, Sp, Naturals, Comma, Sp,
        D(2), Sp, Le, Sp, N, Sp, Implies, Sp, Factorial, Sp, Lt, Sp, PhiCard);
    private static Formula ResultFormula() => Seq(Limit, Sp, Land, Sp, Par(Strictness));
}
