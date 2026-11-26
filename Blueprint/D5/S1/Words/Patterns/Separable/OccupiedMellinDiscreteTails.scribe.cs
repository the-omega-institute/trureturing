using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinDiscreteTailsDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Parens(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula A => F.Id("a");
    private static Formula I => F.Id("i");
    private static Formula K => F.Id("K");
    private static Formula M => F.Id("M");
    private static Formula N => F.Id("n");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Half => Ratio(D(1), D(2));
    private static Formula OriginIndex => Seq(I, Plus, D(1));
    private static Formula TailIndex => Seq(M, Plus, I, Plus, D(1));
    private static Formula Mass(Formula j) => Abs(Call("sample", Beta, A, Ratio(j, N)));
    private static Formula Allowance(Formula k, Formula q, Formula p) =>
        Seq(k, Cdot, Sp, Pow(Parens(Ratio(q, N)), p));

    private static Formula All(Formula cutoff, Formula hypotheses, Formula conclusion) =>
        Seq(Open, Forall, Sp, Beta, Comma, A, InMacro, Sp, Reals, Comma, Sp,
            N, Comma, cutoff, InMacro, Sp, Naturals, Comma, Quad,
            hypotheses, Longrightarrow, RowBreak, Grp(), Quad, Sp, conclusion, Close);

    private static Formula TailBounds() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        All(K, Seq(D(0), Le, Beta, Le, Ratio(D(3), D(4)), Sp, Land, Sp,
                D(0), Le, Sp, A, Sp, Land, Sp, D(0), Lt, N, Sp, Land, Sp, Ratio(K, N), Le, Half),
            Seq(Ratio(D(1), N), Sum, Underscore, Grp(D(0), Le, Sp, I, Lt, K), Mass(OriginIndex),
                Le, Allowance(D(3, 2), K, Ratio(D(3), D(2))))),
        Sp, Land, RowBreak, Grp(),
        All(M, Seq(D(0), Le, Beta, Sp, Land, Sp, D(0), Le, Sp, A, Sp, Land, Sp,
                D(0), Lt, N, Sp, Land, Sp, D(2), Le, Ratio(M, N)),
            Seq(Call("Summable", Seq(I, Mapsto, Mass(TailIndex))), Sp, Land, Sp,
                Ratio(D(1), N), Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty), Mass(TailIndex),
                Le, Allowance(D(4), M, Seq(Minus, Half)))),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The paired shifted Mellin mesh has controlled absolute mass at both integer ends.",
        H("Discrete origin and far tails"),
        Blocks(Describe.Lean(
            DescribeId.Create("discrete-mellin-tail-bounds"),
            DeclarationHandle.Create(
                "D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails.discrete_mellin_tail_bounds"),
            H("Two absolute bounds with exact mesh indices"),
            StatementSource.FromAuthor(TailBounds()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The origin sum contains the points from 1/n through K/n and is empty for K equal to zero. "
                    + "The far sequence starts at (M+1)/n, strictly above M/n. "
                    + "Ratios are real and both estimates allow any nonnegative shift.")),
                Paragraph(Text(
                    "For the origin prefix the square-root pointwise bound can be evaluated at the last point "
                    + "and multiplied by the number of terms. For the far tail the summable power majorant "
                    + "decreases; comparison of its right-endpoint sum to its integral gives the displayed bound. "
                    + "No estimate at the central sample is used."))),
            DescribeRole.Theorem))));
}
