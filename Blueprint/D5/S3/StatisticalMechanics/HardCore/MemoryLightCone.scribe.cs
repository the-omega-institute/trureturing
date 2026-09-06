using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MemoryLightConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite geometric memory exactly reproduces complete deletion counts within its light cone.",
        H("Finite-Depth Exactness of Geometric Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-grid-radius"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.gridRadius"),
                H("Manhattan radius"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The radius is the sum of the natural absolute values of the two integer coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-recenter-radius-bound"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.recenter_radius_bound"),
                H("One step changes distance by at most one toward the origin"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every grid point and every allowed direction, the previous radius is at most the recentered radius plus one. The proof applies the integer absolute-value triangle inequality to the actual three coordinate maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-agree-within"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.AgreeWithin"),
                H("Local equality of blocker membership"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two complete finite sets may differ outside the specified disk. Agreement means equality of membership for every point inside the disk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memory-agreement-step"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.memoryStep_agreeWithin"),
                H("Agreement propagates to the smaller light cone"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Agreement through radius n plus one implies agreement through radius n after the same deletion and recentering. Both retained radii need only be at least n. Equality of the full memories is not required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-complete-blocker-step"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.completeStep"),
                H("The complete accumulation of deleted vertices"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This transition uses the same ordered deletions and coordinate map as geometricStep, retaining every old blocker. There is no spatial truncation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-finite-horizon-exact"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.finite_horizon_exact"),
                H("Radius at least depth gives exact complete counts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every fixed depth n, a retention radius at least n gives exactly the complete count if initial membership agrees through radius n. Both computations use the same history-based ordering. The result permits arbitrary initial finite blocker sets and arbitrary direction histories. It does not interchange the radius and depth limits or prove convergence of asymptotic growth rates."))),
                DescribeRole.Theorem)))));
}
