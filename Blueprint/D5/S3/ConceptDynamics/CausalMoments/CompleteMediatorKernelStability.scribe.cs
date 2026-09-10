using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class CompleteMediatorKernelStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational nonfair outcome transport on the original complete-mediation model.",
        H("CompleteMediatorKernelStability"),
        Blocks(
            Paragraph(Text("All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.")),
            Describe.Lean(DescribeId.Create("kerneldrift"),
                DeclarationHandle.Create(Prefix + "kernelDrift"), H("Keep the signed directed contribution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The drift is half the sum of treated-minus-control mediator mass times the target-minus-source outcome mean."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sensitivityweight"),
                DeclarationHandle.Create(Prefix + "sensitivityWeight"), H("Exclude forced self-pair mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight is one minus the absolute value of combined mediator mass minus one. It is the maximal singleton cut allowed by the original marginals."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kernelradius"),
                DeclarationHandle.Create(Prefix + "kernelRadius"), H("Uniform off-diagonal sensitivity radius"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Half the weighted sum of absolute coordinate changes bounds the centered objective change for every compatible mediator coupling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kerneldrift-swap"),
                DeclarationHandle.Create(Prefix + "kernelDrift_swap"), H("Reverse the signed drift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exchanging source and target reverses the drift sign."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kernelradius-swap"),
                DeclarationHandle.Create(Prefix + "kernelRadius_swap"), H("Symmetric transport radius"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exchanging source and target leaves the radius unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("completemediatorbenefit-mean-identity"),
                DeclarationHandle.Create(Prefix + "completeMediatorBenefit_mean_identity"), H("Original causal cut identity with original means"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual benefit equals half the expected cut plus half the mean drift determined by the original mediator marginals. No fairness premise is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-uniform-kernel-transport"),
                DeclarationHandle.Create(Prefix + "exists_uniform_kernel_transport"), H("One construction controls the entire coupling family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moved outcome law is chosen before quantifying over mediator couplings. It has the prescribed target means and obeys the drift-corrected bound for every original coupling with the nominated marginals."))), DescribeRole.Theorem))));
}
