using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ExactPendantObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ExactPendantObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pendant arcs obstruct finite positive expansivity of exact maps",
        H("Pendant arcs obstruct finite positive expansivity of exact maps"),
        Blocks(
            Paragraph(Text("A pendant arc is an embedded closed interval whose image with the attachment endpoint removed is open in the carrier. Topological exactness means that some positive iterate of each nonempty open set covers the carrier.")),
            Describe.Lean(
                DescribeId.Create("exact-pendant-arbitrary-coalescing-families"),
                DeclarationHandle.Create(Owner + "coalescing_witnesses"),
                H("Arbitrarily large families coalesce at every positive scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a compact metric space contain a pendant arc, and let its continuous selfmap be topologically exact. For every positive radius and finite cardinality there is an injectively indexed family whose orbits are pairwise strictly closer than that radius at all forward times. All points in the family have a common image at one finite time.")),
                    Paragraph(Text("Exactness makes an iterate reach the leaf from the interior of any pendant subarc. With finite fibers, the two sides of a preimage of the leaf both map over a common smaller subarc. Shrink the source to control the finite orbit prefix, then lift the inductive family through both sides. An infinite fiber already supplies arbitrarily large families in one small ball."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-pendant-obstruction"),
                DeclarationHandle.Create(Owner + "not_finitelyPositiveExpansive"),
                H("Exact dynamics excludes finite positive expansivity on a pendant arc carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a continuous topologically exact selfmap of a compact metric space with a pendant arc, the coalescing families rule out every finite uniform bound on strict forward Bowen sets. A finite graph with a leaf has such an arc."))),
                DescribeRole.Theorem))));
}
