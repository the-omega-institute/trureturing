using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class TwoMomentSupportHoleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/TwoMomentSupportHole.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving probability atoms determine the exact price of excluding a support interval from a noisy two-moment model.",
        H("Two-Moment Support Hole"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-moment-support-hole-feasible-masses"),
                DeclarationHandle.Create(Prefix + "twoMomentMassSet"),
                H("Actual finite probability pairs"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The designated atom is at one. Residual nodes lie in [a,1), outside the specified hole, and comparison nodes lie in [a,b]. Both measures have nonnegative weights and total mass one. The first two actual Prony moments differ by at most epsilon. Arbitrary finite cardinalities are allowed, and the exclusion of one from residual nodes makes w the actual endpoint mass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-moment-support-hole-sharp-loss"),
                DeclarationHandle.Create(Prefix + "two_moment_support_hole_sharp"),
                H("Attained maxima and exact support-loss law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the stated continuous geometric parameters, epsilon=(1-b)(b-t)/(2+t) yields a moving residual atom at t in the unrestricted optimizer. Excluding (l,r) replaces it by explicit nonnegative masses at l and r. Both optimizers are normalized and saturate the actual first two moment errors. Quadratic certificates bound all competing finite laws and yield two IsGreatest conclusions. Their exact difference is (1-wc)(t-l)(r-t)/((1-l)(1-r)), including boundary zero loss. The complete all-noise curve, fixed-grid consequence and optimal transformed grid have ordinary proofs in the theory; this declaration formalizes the general moving-support and hole comparison."))),
                DescribeRole.Theorem))));
}
