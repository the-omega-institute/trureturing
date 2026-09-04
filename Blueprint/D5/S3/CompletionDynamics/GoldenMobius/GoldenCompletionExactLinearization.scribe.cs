using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenCompletionExactLinearizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/CompletionDynamics/GoldenMobius/GoldenCompletionExactLinearization."
        + "golden_completion_exact_linearization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden cross-ratio linearization extends exactly through every defined finite iterate.",
        H("Golden Completion Exact Linearization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-completion-exact-linearization"),
            DeclarationHandle.Create(Declaration),
            H("Exact Linearization at Every Finite Depth"),
            StatementSource.FromAuthor(ExactLinearizationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first clause gives the exact one-step cross-ratio multiplier on the "
                    + "real affine chart. The second gives the exact multiplier power for every "
                    + "finite iterate whose earlier orbit points remain in that chart.")),
                Paragraph(Text(
                    "The map, cross-ratio coordinate, and multiplier are the canonical objects "
                    + "from the GoldenMobius family; the domain premises exclude only their "
                    + "displayed affine-chart poles."))),
            DescribeRole.Theorem))));

    private static Formula ExactLinearizationFormula()
    {
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula goldenConj = Seq(F.Id("Real"), Dot, F.Id("goldenConj"));
        Formula multiplier = F.Id("goldenProjectiveMultiplier");

        Formula MobiusIterate(Formula exponent) =>
            Seq(Open, F.Id("goldenMobius"), Caret,
                Grp(OpenBracket, exponent, CloseBracket), Close, Sp, x);

        Formula oneStep = Seq(
            Forall, Sp, x, Colon, Sp, real, Comma, RowBreak, Grp(),
            Open, x, Sp, Neq, Sp, D(0), Close, Sp, Land, Sp,
            Open, x, Sp, Neq, Sp, goldenConj, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open,
            Call("goldenCrossRatio", Call("goldenMobius", x)), Sp, Eq, Sp,
            multiplier, Sp, Times, Sp, Call("goldenCrossRatio", x),
            Close);

        Formula orbitDomain = Seq(
            Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            k, Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
            Open, MobiusIterate(k), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            MobiusIterate(k), Sp, Neq, Sp, goldenConj, Close);

        Formula finiteDepth = Seq(
            Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
            x, Colon, Sp, real, Comma, RowBreak, Grp(),
            Open, orbitDomain, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Call("goldenCrossRatio", MobiusIterate(n)), Sp, Eq, Sp,
            multiplier, Sp, Caret, Grp(n), Sp, Times, Sp,
            Call("goldenCrossRatio", x),
            Close);

        return Disp(Seq(
            Open, oneStep, Close, Sp, Land, RowBreak, Grp(),
            Open, finiteDepth, Close));
    }
}
