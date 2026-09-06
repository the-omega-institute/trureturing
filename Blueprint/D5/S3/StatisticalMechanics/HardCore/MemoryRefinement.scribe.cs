using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MemoryRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compare retained geometric memories using the same actions and an explicit controller transport.",
        H("Geometric Memory Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-geometric-step"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.geometricStep"),
                H("The geometric transition before finite encoding"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A child is present exactly when its direction is outside the recorded blocked set. Its next state is the existing radius-truncated geometric update."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memory-step-monotone"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.memoryStep_mono"),
                H("Larger retained geometry preserves blocker inclusion"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both the initial blocked set and retention radius increase. The ordering and chosen direction remain the same. Union, image and nested radius filters preserve inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-history-count-antitone"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.history_count_antitone"),
                H("Shared history-based ordering gives fewer refined paths"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every depth and initial history, inclusion of blockers and radii reverses the descendant-count inequality. Both trees use the same history-based order. No assertion compares independently optimized state policies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-coupled-memory-step"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupledStep"),
                H("Retain the coarse controller state explicitly"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state retains both coarse and refined blocked sets. Refined blockers decide child availability; both sets receive the chosen action. The coarse set is not reconstructed from the refined set by radius projection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-coupled-controller-count"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupled_count_le_coarse"),
                H("Transport every coarse controller without increasing counts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coarse policy may depend on the complete direction history and its actual coarse blocked set. The coupled policy reads precisely those same inputs. At each shared child, blocker inclusion is preserved, so induction proves the all-depth inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-fixed-presentation-count"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.fixed_presentation_count"),
                H("Exact fixed-order finite-presentation semantics"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Direction-preserving equality of represented and geometric transitions gives equality of every fixed-order descendant count. Only transitions of the chosen order need closure. Multiple child directions retain their multiplicities. The radius-four certificate supplies the concrete consumer."))),
                DescribeRole.Theorem)))));
}
