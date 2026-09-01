using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class OrbitVarianceRiemannCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/OrbitVarianceRiemannCriterion."
            + "orbit_variance_rh_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vanishing finite-height completion variance characterizes the abstract "
            + "critical-line condition under explicit coverage and positive-multiplicity "
            + "premises.",
        H("Orbit-Variance RH Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("orbit-variance-rh-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Zero orbit variance is equivalent to the critical-line condition"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, Xi, Colon, Sp,
                Mathbb, Grp(F.Id("C")), Sp, To, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                Mu, Colon, Sp,
                Mathbb, Grp(F.Id("C")), Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                F.Id("W"), Comma, Esc,
                Open, Forall, Sp, Rho, Comma, Sp,
                Xi, Open, Rho, Close, Eq, D(0), Sp, Land, Sp,
                D(0), Lt, Operatorname, Grp(F.Id("Im")), Open, Rho, Close,
                Sp, Rightarrow, Sp, D(0), Lt, Mu, Open, Rho, Close, Close,
                Sp, Rightarrow, Esc,
                Open, Forall, Sp, Rho, Comma, Sp, Xi, Open, Rho, Close, Eq, D(0),
                Sp, Rightarrow, Sp, Exists, Sp, Sigma, Comma, Sp,
                Xi, Open, Sigma, Close, Eq, D(0), Sp, Land, Sp,
                D(0), Lt, Operatorname, Grp(F.Id("Im")), Open, Sigma, Close,
                Sp, Land, Sp,
                Operatorname, Grp(F.Id("Re")), Open, Sigma, Close, Eq,
                Operatorname, Grp(F.Id("Re")), Open, Rho, Close, Close,
                Sp, Rightarrow, Esc,
                Open, Operatorname, Grp(F.Id("CLH")), Open, Xi, Close,
                Sp, Leftrightarrow, Sp,
                Forall, Sp, F.Id("T"), Comma, Sp, D(0), Lt, F.Id("T"),
                Sp, Rightarrow, Sp,
                Operatorname, Grp(F.Id("completionVariance")),
                Open, F.Id("W"), Open, F.Id("T"), Close, Comma, Sp, Mu, Close,
                Eq, D(0), Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every positive height, a finite zero window records exactly the "
                        + "positive-ordinate zeros below that height. Multiplicities are "
                        + "required to be positive at those zeros, so every off-line zero "
                        + "in a window contributes a strictly positive summand.")),
                Paragraph(Text(
                    "Mathlib's nonnegative finite-sum criterion gives that the variance "
                        + "vanishes exactly when every multiplicity-weighted squared "
                        + "critical displacement vanishes. Choosing T=Im(rho)+1 detects "
                        + "each positive-ordinate off-line zero.")),
                Paragraph(Text(
                    "Because the imported window definition only contains zeros with "
                        + "positive ordinate, the all-zero statement explicitly assumes "
                        + "that every zero's real part has a positive-ordinate "
                        + "representative. The assumption is visible rather than hidden "
                        + "inside the critical-line predicate.")),
                Paragraph(Text(
                    "Two concrete checks exclude vacuity: the imported xi(rho)=rho-i "
                        + "witness has variance 1/4 at height two, while a singleton zero "
                        + "at 1/2+i lies on the critical line and has variance zero."))),
            DescribeRole.Theorem))));
}
