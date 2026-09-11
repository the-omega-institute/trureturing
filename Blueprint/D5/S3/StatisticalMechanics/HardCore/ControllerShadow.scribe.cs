using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class ControllerShadowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport state-dependent geometric controllers by replaying their coarse history.",
        H("Constructed controller shadows"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-controller-trace"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.controllerTrace"),
                H("Coarse history replay"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The newest-first direction history determines a coarse mask by replaying actual memoryStep updates. The function is total on illegal histories; only legal branches contribute to path counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-lifted-policy"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.liftedPolicy"),
                H("A constructed history policy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fine controller reads the replayed coarse mask. It never substitutes the current fine mask's projection for forgotten coarse history."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-lifted-controller-refines"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.lifted_controller_refines"),
                H("All-depth refinement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nested initial blocker sets and increasing radius, the constructed history policy has no more fine-memory descendants than the original coarse state policy. MemoryRefinement owns the synchronized-history comparison and is reused."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-coarse-shadow-projection-failure"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_is_not_current_projection"),
                H("An exact legal geometric diagnostic"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chronological SRL walk straight, straight, right, right is legal in both radii. The point (2,-1) remains in the radius-four state after projection into the radius-three disk, but the radius-three process has already forgotten it. The finite proof script requests kernel reduction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-coarse-shadow-current-projection-claim"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.CoarseShadowIsCurrentProjection"),
                H("The current projection claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim quantifies over every state-dependent controller, initial blocker set and newest-first history: the radius-three trace equals the radius-four trace filtered by Manhattan distance at most three."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-coarse-shadow-current-projection-refutation"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_refutes_current_projection"),
                H("Refutation of current projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Instantiate the claim at the constant-zero controller, the parent-blocked initial set and history [1, 1, 0, 0]. The existing legal witness places (2,-1) in the filtered fine trace and outside the coarse trace, contradicting equality."))), DescribeRole.Theorem),
            Paragraph(Text("This source is a logically reviewed candidate. Lean elaboration, executed axiom closure and Scribe emission have not been obtained in the authoring runtime.")))));
}
