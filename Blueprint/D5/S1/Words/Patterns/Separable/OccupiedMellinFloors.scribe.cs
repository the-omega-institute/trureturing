using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinFloorsDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula I => F.Id("i");
    private static Formula N => F.Id("n");
    private static Formula R => F.Id("R");
    private static Formula S => F.Id("s");
    private static Formula Reals => Seq(Mathbb, Grp(R));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Domain => Seq(Open, D(0), Comma, Infty, Close);
    private static Formula ShiftedSample => Call("sample", Beta, Ratio(D(2), N), Ratio(Seq(I, Plus, D(1)), N));
    private static Formula UnshiftedSample => Call("sample", Beta, D(0), S);

    private static Formula Estimate() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, Beta, InMacro, Sp, Reals, Comma, Sp, N, InMacro, Sp, Naturals, Comma, RowBreak, Grp(),
        D(0), Le, Beta, Le, Ratio(D(3), D(4)), Sp, Land, Sp,
        Pow(D(4), D(2, 0)), Le, Sp, N, Longrightarrow, RowBreak, Grp(),
        Call("Summable", Seq(I, Mapsto, Abs(ShiftedSample))), Sp, Land, Sp,
        Call("IntegrableOn", Seq(S, Mapsto, UnshiftedSample), Domain), Sp, Land, RowBreak, Grp(),
        Abs(Seq(Int, Underscore, Grp(Domain), UnshiftedSample, Thin, F.Id("ds"), Minus,
            Ratio(D(1), N), Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty), ShiftedSample)),
        Le, D(1, 2, 3, 2), Cdot, Sp, Pow(N, Seq(Minus, Ratio(D(1), D(8, 0)))),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural floor cutoffs give a uniform algebraic rate for the shifted Mellin quadrature.",
        H("Integer cutoffs for paired Mellin quadrature"),
        Blocks(Describe.Lean(
            DescribeId.Create("algebraic-mellin-mesh-rate"),
            DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinFloors.global_mesh_rate"),
            H("Uniform error at the natural mesh resolution"),
            StatementSource.FromAuthor(Estimate()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All ratios and variable powers are real; the threshold is the natural number four to the twentieth. "
                    + "The integral is unshifted and uses Lebesgue measure on the positive half-line. "
                    + "The mesh starts at index one and uses the exact shift 2/n.")),
                Paragraph(Text(
                    "Write q for n to the power minus one twentieth. The two integer cutoffs are the natural "
                    + "floors of n times q and n divided by q. Floor inequalities bound the first normalized cutoff "
                    + "between q/2 and q, and the far cutoff after subtracting one by q inverse divided by two from below. "
                    + "The resulting mesh budget has each term bounded by a multiple of n to the power minus one eightieth."))),
            DescribeRole.Theorem))));
}
