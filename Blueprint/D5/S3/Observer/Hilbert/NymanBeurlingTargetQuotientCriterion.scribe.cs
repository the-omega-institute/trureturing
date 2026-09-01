using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanBeurlingTargetQuotientCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion."
            + "nyman_beurling_target_quotient_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Nyman-Beurling membership criterion is equivalent to quotient, residual-projection, "
            + "and finite-stage distance criteria in an abstract Hilbert space.",
        H("Nyman-Beurling Target Quotient Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("nyman-beurling-target-quotient-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Five equivalent Nyman-Beurling target criteria"),
            StatementSource.FromAuthor(CriterionStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The analytic Nyman-Beurling theorem is an explicit hypothesis connecting "
                        + "the abstract proposition RH to membership in the closed cumulative "
                        + "space; the formalization does not define RH by that membership.")),
                Paragraph(Text(
                    "The remaining equivalences are proved from Hilbert-space geometry: the "
                        + "quotient class vanishes exactly on the subspace, projection onto its "
                        + "orthogonal complement vanishes exactly on the closed subspace, and "
                        + "distances to a monotone tower tend to zero exactly on its closed union.")),
                Paragraph(Text(
                    "Constant coordinate-line towers in the real Euclidean plane witness both "
                        + "the simultaneously true and the simultaneously false cases."))),
            DescribeRole.Theorem))));

    private static Formula CriterionStatement()
    {
        Formula chi = F.Id("chi");
        Formula cumulativeSpace = Seq(F.Id("S"), Underscore, Grp(Infty));
        Formula stageSpace = Seq(F.Id("S"), Underscore, Grp(F.Id("N")));
        Formula quotientClass = Seq(
            OpenBracket, chi, CloseBracket, Underscore,
            Grp(F.Id("H"), Slash, cumulativeSpace));
        Formula residualProjection = Seq(
            Operatorname, Grp(F.Id("starProjection")), Underscore,
            Grp(cumulativeSpace, Caret, Grp(Perp)), Open, chi, Close);
        Formula distanceLimit = Seq(
            Operatorname, Grp(F.Id("Tendsto")), Open,
            LambdaLower, Sp, F.Id("N"), Comma, Sp,
            Operatorname, Grp(F.Id("infDist")), Open,
            chi, Comma, Sp, stageSpace, Close,
            Comma, Sp, F.Id("atTop"), Comma, Sp,
            Operatorname, Grp(F.Id("nhds")), Open, D(0), Close, Close);

        return Disp(Seq(
            F.Id("RH"), Sp, Leftrightarrow, Sp,
            chi, Sp, InMacro, Sp, cumulativeSpace, Sp, Leftrightarrow, Sp,
            quotientClass, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            residualProjection, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            distanceLimit));
    }
}
