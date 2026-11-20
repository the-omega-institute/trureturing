using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class FiniteGraphAffineRealizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine realization of a finite simple graph",
        H("Affine realization of a finite simple graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-graph-edge-distance"),
                DeclarationHandle.Create(Owner + "dist_edgeChart_incident"),
                H("Distance between incident edge germs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a shared vertex, the sup distance between points on two different edges is the maximum of their parameters measured from that vertex. The two distinct endpoint coordinates attain the required lower bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affine-graph-open-leaf-tip"),
                DeclarationHandle.Create(Owner + "tip_eq_pos_coord"),
                H("The tip of a leaf edge is open"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive leaf coordinate singles out the part of the unique incident edge away from its attachment. This yields the pendant arc used in the obstruction."))),
                DescribeRole.Theorem))));
}
