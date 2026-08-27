using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class MemorylessActionObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated public states with different actions rule out a memoryless policy.",
        H("Memoryless Action Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("no-memoryless-policy"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.no_memoryless_policy"),
            H("A repeated public state cannot support two different actions"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The public-state map and action trace are source primitives. If two times "
                    + "have the same public state but distinct actions, any policy depending "
                    + "only on that public state would assign equal actions at those times, "
                    + "contradicting the observed action inequality."))),
            DescribeRole.Theorem))));

}
