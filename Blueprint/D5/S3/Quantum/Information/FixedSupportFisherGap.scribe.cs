using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FixedSupportFisherGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FixedSupportFisherGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized probability curve on one fixed finite support has a strict Fisher-information gap.",
        H("Fixed-support Fisher gap"),
        Blocks(
            Paragraph(Text(
                "Let ι be any finite index type. The same support values x(j) and the same "
                + "nonnegative weight curve p(j,u) are used for every parameter u in the open "
                + "interval (2a−1,1). The curve is normalized, has mean a, and has second "
                + "moment (1+u)/2 throughout that interval. The Fisher sum is filtered to the "
                + "indices with positive current weight; indices of weight zero contribute zero "
                + "because nonnegative differentiable weights have zero derivative at a local "
                + "minimum.")),
            Describe.Lean(
                DescribeId.Create("fixed-support-fisher-gap-result"),
                DeclarationHandle.Create(Module + "result"),
                H("The exact gap"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume 0<a<1, every support point lies in [−1,1], every weight is "
                        + "DifferentiableOn on (2a−1,1), and the displayed normalization and two "
                        + "moment identities hold for the same curve at every parameter. If its "
                        + "actual positive-support Fisher sum is at most R(1−a²)/((1−u)(1+u−2a²)) "
                        + "pointwise, then R is at least 1+a² divided by "
                        + "(1+4a+2(1+a) log 2)². The conclusion is uniform over the arbitrary "
                        + "finite fixed support and does not assume endpoint continuity or a "
                        + "limiting value of p.")),
                    Paragraph(Text(
                        "The proof differentiates the three same-curve constraints, applies the "
                        + "finite weighted Cauchy–Schwarz inequality with zero-weight terms removed, "
                        + "and controls the resulting normalized mean along the interval. Monotonicity "
                        + "and continuity of the auxiliary expressions at the left endpoint produce "
                        + "the exact log 2 constant.")),
                    Paragraph(Text(
                        "For nonvacuity, the support [−1,1/2,1] with a=1/2 and R=4/3 and weights "
                        + "((1+2u)/12, 2(1−u)/3, (1+2u)/4) satisfies all hypotheses on (0,1); "
                        + "all three weights are strictly positive there, so the filtered Fisher "
                        + "sum is the full three-term sum.")))))));

    private static Formula ResultFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("iota"), Sp, F.Id("a"), Comma, Sp, F.Id("R"), Comma, Sp,
            F.Id("x"), Comma, Sp, F.Id("p"), Sp, Colon, Sp,
            Mathbb, Sp, F.Id("R"), Sp, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, F.Id("a"), Sp, Lt, Sp, D(1), Close,
            Sp, Longrightarrow, Sp,
            D(1), Sp, Plus, Sp,
            Quotient(F.Id("a"), Grp(D(1), Plus, D(4), F.Id("a"), Plus, D(2),
                Open, D(1), Plus, F.Id("a"), Close, Log, Sp, D(2))),
            Sp, Le, Sp, F.Id("R")));

    private static Formula Quotient(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
}
