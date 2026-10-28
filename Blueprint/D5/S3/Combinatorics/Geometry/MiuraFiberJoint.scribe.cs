using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberJointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberJoint.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint indexed reconstruction on actual residual arrays.", H("Entire row and column vectors on one realization"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafiberjoint-0"),
                DeclarationHandle.Create(Prefix + "JointExtremaExpansion"), H("Both cumulative coordinates of every extremum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each actual expanded cell, strict minimum status is equivalent to coming from an original strict minimum with both coordinates equal to the corresponding cumulative insertion coordinates. The equivalence is also imposed separately for maxima. Every original cell and every full physical neighbour remains interpreted on its actual rectangle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurafiberjoint-1"),
                DeclarationHandle.Create(Prefix + "indexed_joint_expansion"), H("Simultaneous realization of both complete vectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given an actual residual array with both dimensions at least two, prescribe natural extra-copy coordinates at every original row and column, supported on genuinely frozen lines on the corresponding axis. One actual normalized unit-edge array exists at dimensions m plus the row-vector sum and n plus the column-vector sum. It retains the exact residual split and common-side exclusion, reduces to the original array by legal joint deletions, and transports every individual minimum and maximum to both prescribed cumulative coordinates. Column expansion preserves occupied original rows; the actual inactive-row criterion then makes all prescribed row insertions available in the same realization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miurafiberjoint-2"),
                DeclarationHandle.Create(Prefix + "indexed_joint_weights_unique"), H("Read back every coordinate on both axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix an actual unit-edge core with both dimensions at least two and no adjacent frozen pair on either axis. If two supported row vectors and two supported column vectors have the same corresponding output dimensions and the same actual output function satisfies both joint extremum expansions, the entire row vectors agree and the entire column vectors agree. The exact occupied images are read from that one output and the one-axis readback theorem is applied to both physical axes. No choice-independent canonical-core theorem and no fiber cardinality are assumed."))), DescribeRole.Theorem))));
}
