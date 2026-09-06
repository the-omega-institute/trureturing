using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RadiusThreeDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core branching, exact certificates and their precise scope.",
        H("RadiusThreeData"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreedata-radiusthreerows"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeData.radiusThreeRows"),
                H("Exact masks, weights and controller"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete data expand losslessly from packed masks and a shared table of integer weight triples. The mathematical states are blocked vertex sets. Packing is only a storage representation; it is not state minimization. No verdict from an external solver is stored as a hypothesis."))),
                DescribeRole.Definition),
            Paragraph(Text("The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.")))));
}
