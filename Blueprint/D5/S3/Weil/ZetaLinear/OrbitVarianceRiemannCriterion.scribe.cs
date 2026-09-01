using static StrataLint.Scribe.DefinitionDsl;

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
            StatementSource.WithoutFormula(),
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
