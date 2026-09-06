using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustAffinityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustAffinity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A certified robust Ramsey separation margin gives an explicit Bhattacharyya affinity ceiling for the one-shot chronology laws.",
        H("Golden Robust Affinity"),
        Blocks(
            Paragraph(Text(
                "This module composes three existing layers: deterministic calibration "
                    + "margins, exact Bernoulli total variation, and the generic "
                    + "variation-margin-to-affinity theorem. It adds no new information "
                    + "inequality.")),
            Describe.Lean(
                DescribeId.Create("robust-margin"),
                DeclarationHandle.Create(Prefix + "robustSeparationMargin"),
                H("Certified robust separation margin"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The margin is the nominal fringe gap minus the two word-specific calibration budgets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("robust-affinity-ceiling"),
                DeclarationHandle.Create(Prefix + "robust_bhattacharyya_le_margin_ceiling"),
                H("Robust margin bounds one-shot affinity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When both robust fringes are valid probabilities and the certified margin is nonnegative, their Bhattacharyya affinity is at most sqrt(1-margin squared)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The remaining finite-shot step is now purely compositional: multiply the "
                    + "one-shot affinity across repeated independent coordinates and reuse "
                    + "the repository's existing finite-suite optimal-error upper bound."))))));
}
