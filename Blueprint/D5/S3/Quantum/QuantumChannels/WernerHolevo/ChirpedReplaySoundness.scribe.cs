using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedReplaySoundnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Soundness of integer replay for a preconditioned root certificate.",
        H("Soundness of integer replay for a preconditioned root certificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("clm-bounds-of-rows"),
                DeclarationHandle.Create(Module + ".clm_bounds_of_rows"),
                H("Integer rows bound the real operator norms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Uniform scaled errors for the integer residual and Jacobian enlarge the row bounds for the "
                    + "preconditioned step and the derivative defect. The row sums also bound the preconditioner in "
                    + "the operator norm induced by the coordinate sup norm."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-unique-zero-of-replay"),
                DeclarationHandle.Create(Module + ".existsUnique_zero_of_replay"),
                H("Strict integer comparisons certify a unique root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scaled residual and Jacobian bounds, integer row bounds and two strict comparisons imply "
                    + "existence and uniqueness in the closed ball of radius 2⁻³⁰. The theorem requires the derivative "
                    + "of the exact residual throughout the ball and the stated derivative drift estimate."))),
                DescribeRole.Theorem))));
}
