using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingMixedComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed weaving circles and spanning components.", H("Mixed weaving circles and spanning components"), Blocks(
            Paragraph(Text("Let P have n at least two and m at least three, with cyclic time ZMod(m). For either parity p below two and any subset S of crossings, use the complementary local smoothing precisely at S and retain the actual external matching. The resulting quotient MixedCircle contains all components, including those meeting the closing seam. The reference graph has every uniform circle as a vertex and exactly the crossing incidences selected by S.")),
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/WeavingMixedComponents.mixedComponentMap_surjective"),
                H("Mixed weaving circles and spanning components"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sending a dart to its uniform circle and then to its spanning-graph component is constant on each actual mixed circle. At a selected crossing all four port classes belong to the same spanning component; at an unselected crossing the original local arc preserves its uniform circle. The external matching preserves that uniform circle as well. The map therefore descends to mixed circles and is onto the full spanning-component quotient, including isolated vertices. Distinct reference components consequently force distinct mixed circles. With every crossing selected the reference graph is connected: the actual wires connect consecutive generator positions, and the left seam advances cyclic time."))), DescribeRole.Theorem),
            Paragraph(Text("These finite matching statements are auxiliary to weaving coefficient asymptotics. They do not identify a state polynomial with the source trace-defined Jones invariant or establish the original twist-number limit.")))));
}
