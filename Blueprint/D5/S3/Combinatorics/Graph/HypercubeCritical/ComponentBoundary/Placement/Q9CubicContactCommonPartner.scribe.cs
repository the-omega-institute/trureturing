using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9CubicContactCommonPartnerDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two endpoint translations exclude a single common partner of two cubic contact axes.",
        H("An obstruction from overlapping coordinate translations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-single-common-partner"),
                DeclarationHandle.Create(Placement + "Q9CubicContactCommonPartner.no_single_common_partner"),
                H("Two cubic contact axes cannot have exactly one common partner"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consider a realized contact on axes i and j. The other partners of i are a and d, and those of j are c and d. Translate the contact by c and d and inspect its midpoint reached along i. The original contact and its translate by a and d rule out the two additional opposite-side neighbors. Either neighbor would realize the missing pair i and c. The midpoint then has one neighbor on the opposite support and violates exterior parity."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DegreeThreeContactOrbit"))]));
}
