using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class InactiveArchiveFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinite Historical Fibers.",
        H("Infinite Historical Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inactivearchivefibers-infinite-fibre"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/InactiveArchiveFibers.infinite_fibre"),
                H("Isolated inactive extensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In every finite dimension, any rich history has an injective family of extensions "
                    + "indexed by the natural numbers. The extension at index k adds exactly k isolated "
                    + "inactive events. An inclusion preserves every old event name, attribute and causal "
                    + "relation, and maps the current region and selected subset exactly onto those of "
                    + "the extension. Selected and background charges are unchanged. Distinct indices "
                    + "give different archive cardinalities, excluding historical isomorphisms. "
                    + "The construction also applies to empty archives and empty selections."))),
                DescribeRole.Theorem))));
}
