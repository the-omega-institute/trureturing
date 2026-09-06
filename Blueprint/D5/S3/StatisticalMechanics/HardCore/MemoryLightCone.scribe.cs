using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MemoryLightConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core memory, exact path semantics and integer certificates.",
        H("Finite-Depth Exactness of Geometric Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-gridradius"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.gridRadius"),
                H("Manhattan radius"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The radius is the sum of the natural absolute values of the integer coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-recenter-radius-bound"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.recenter_radius_bound"),
                H("Finite propagation speed"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every old radius is at most the recentered radius plus one. The proof uses the integer triangle inequality and the actual three coordinate maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-agreewithin"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.AgreeWithin"),
                H("Local blocker agreement"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership agrees for every point in the specified disk; the sets may differ arbitrarily outside it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-memorystep-agreewithin"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.memoryStep_agreeWithin"),
                H("Agreement on the smaller light cone"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Agreement through radius n plus one implies agreement through radius n after the same update, when both retention radii are at least n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-completestep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.completeStep"),
                H("Complete blocker accumulation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the same deletion and recentering without forgetting any old blocker."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-memorylightcone-finite-horizon-exact"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.finite_horizon_exact"),
                H("Exact complete counts within the horizon"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a common history-based ordering, radius at least n reproduces the complete depth-n count whenever initial blockers agree through radius n. This finite-depth statement alone does not interchange radius and depth limits."))),
                DescribeRole.Theorem))));
}
