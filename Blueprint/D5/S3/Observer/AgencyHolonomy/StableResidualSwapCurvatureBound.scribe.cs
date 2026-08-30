using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class StableResidualSwapCurvatureBoundDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/StableResidualSwapCurvatureBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stable swap curvature is controlled linearly and quadratically by residual local factors.",
        H("Stable Residual Swap Curvature Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stable-residual-swap-curvature"),
                DeclarationHandle.Create(Prefix + "stableResidualSwapCurvature"),
                H("Stable residual swap curvature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write the two scalar local factors as one plus their residuals and "
                        + "their stable-channel memory injections as residual times channel. "
                        + "This definition is the adjacent-swap defect of those two lifted "
                        + "updates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stable-residual-swap-curvature-bound"),
                DeclarationHandle.Create(
                    Prefix + "stable_residual_swap_curvature_bound"),
                H("Residual factors control stable swap curvature"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Over any normed field, assume the two channel coordinates have norm "
                            + "at most one. Expanding the adjacent-swap defect gives one term "
                            + "linear in the residuals and one bilinear correction.")),
                    Paragraph(Text(
                        "The triangle inequality and multiplicativity of the field norm bound "
                            + "the linear term by the sum of the two residual norms and the "
                            + "channel difference by two.")),
                    Paragraph(Text(
                        "If both residual norms are bounded by a common nonnegative envelope, "
                            + "the defect is at most two times the stable gap times that "
                            + "envelope, plus twice its square. No decay of the envelope is "
                            + "assumed here."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula stable = F.Id("a");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula residualQ = new Formula.Subscript(F.Id("r"), F.Id("q"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula channelQ = new Formula.Subscript(F.Id("v"), F.Id("q"));
        Formula envelope = Varepsilon;
        Formula curvatureName = Seq(F.Id("C"), Underscore, Grp(F.Id("st")));
        Formula curvature = Call(
            curvatureName, stable, residualP, residualQ, channelP, channelQ);
        Formula stableGap = Seq(Open, stable, Sp, Minus, Sp, D(1), Close);
        Formula injectionDifference = Seq(
            Open,
            residualP, Sp, Cdot, Sp, channelP,
            Sp, Minus, Sp,
            residualQ, Sp, Cdot, Sp, channelQ,
            Close);
        Formula channelDifference = Seq(
            Open, channelQ, Sp, Minus, Sp, channelP, Close);
        Formula exactValue = Seq(
            stableGap, Sp, Cdot, Sp, injectionDifference,
            Sp, Plus, Sp,
            residualP, Sp, Cdot, Sp, residualQ,
            Sp, Cdot, Sp, channelDifference);
        Formula normBound = Seq(
            Norm(stableGap), Sp, Cdot, Sp,
            Open, Norm(residualP), Sp, Plus, Sp, Norm(residualQ), Close,
            Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Norm(residualP), Sp, Cdot, Sp, Norm(residualQ));
        Formula envelopeBound = Seq(
            D(2), Sp, Cdot, Sp, Norm(stableGap), Sp, Cdot, Sp, envelope,
            Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Power(envelope, D(2)));
        Formula channelHypotheses = Seq(
            Norm(channelP), Sp, Leq, Sp, D(1),
            Sp, Land, Sp,
            Norm(channelQ), Sp, Leq, Sp, D(1));
        Formula envelopeHypotheses = Seq(
            D(0), Sp, Leq, Sp, envelope,
            Sp, Land, Sp,
            Norm(residualP), Sp, Leq, Sp, envelope,
            Sp, Land, Sp,
            Norm(residualQ), Sp, Leq, Sp, envelope);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, field, Colon, Sp, F.Id("NormedField"), Comma, Sp,
            stable, Comma, Sp, residualP, Comma, Sp, residualQ, Comma, Sp,
            channelP, Comma, Sp, channelQ, Colon, Sp, field, Comma,
            RowBreak, Grp(),
            Open, channelHypotheses, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            curvature, Sp, Eq, Sp, exactValue, Sp, Land,
            RowBreak, Grp(),
            Norm(curvature), Sp, Leq, Sp, normBound, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, envelope, Colon, Sp, Reals(), Comma, Sp,
            Open, envelopeHypotheses, Close, Sp, Rightarrow, Sp,
            Norm(curvature), Sp, Leq, Sp, envelopeBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
