using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MemoryRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core memory, exact path semantics and integer certificates.",
        H("Geometric Memory Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-geometricstep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.geometricStep"),
                H("The geometric transition"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A child is present exactly when its direction is outside the recorded blocked set. Its successor is the existing radius-truncated geometric update."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-memorystep-mono"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.memoryStep_mono"),
                H("Monotone retained geometry"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Increasing the blocked set and radius preserves blocker inclusion under the same ordering and direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-history-count-antitone"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.history_count_antitone"),
                H("Common history-based ordering"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Larger memory has no more descendants at any depth under the same history-based policy. Independently chosen state policies are outside this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-coupledstep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupledStep"),
                H("Retain the coarse controller state"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep both blocked sets. The refined set decides availability; both receive the same action. The coarse state is not recovered by projecting the fine state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-coupled-count-le-coarse"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupled_count_le_coarse"),
                H("Transport an arbitrary coarse controller"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The controller may depend on its coarse state and complete direction history. The coupled implementation reads the same inputs and never increases path counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memoryrefinement-fixed-presentation-count"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.fixed_presentation_count"),
                H("Exact finite-presentation semantics"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Direction-preserving transition equality gives equality of all fixed-order counts. Only the selected order requires closure. Directions retain their multiplicities. RadiusFourCertificates supplies a concrete consumer."))),
                DescribeRole.Theorem))));
}
