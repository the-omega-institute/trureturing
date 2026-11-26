using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactCubeOrdersDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactCubeOrders";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutation coverage for two-contact Huang cube columns",
        H("Permutation coverage for two-contact Huang cube columns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cube-contact-partner-count"),
                DeclarationHandle.Create(Module + ".card_rowContacts_of_occupied"),
                H("The source axes of an occupied partner count its other contacts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The other column at an empty row determines an occupied partner "
                    + "axis at the original column. The opposite corner of the square "
                    + "gives a bijection from the empty source directions with that "
                    + "partner to the other contacts of the occupied row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-triples-count"),
                DeclarationHandle.Create(Module + ".tripleCount_eq_card_threeContactRowsAt"),
                H("Three-axis stars correspond to three-contact occupied rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fibers of the partner map are disjoint. Each fiber together "
                    + "with its occupied target forms one coordinate block. A block "
                    + "has size three precisely when its target row has three "
                    + "selected contacts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-contact-permutation-weighted-cover"),
                DeclarationHandle.Create(Module + ".weighted_order_coverage_of_cube"),
                H("The weighted permutation cover is a necessary cube contact bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With four empty directions per selected column, exactly two "
                        + "contacts at each incident empty row, and at most three at "
                        + "occupied rows, there are four source axes. The partner blocks "
                        + "all have size two or three and carry the integer exponent steps. "
                        + "The permutation covering theorem gives 144 as a lower bound "
                        + "for the weighted sum of the three column counts.")),
                    Paragraph(Text(
                        "This supplies a structural obstruction for the two-contact "
                        + "case in Hong, Wu and Xia's open nine-cube Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactCubeLift")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactOrderCoverage"))
        ]));
}
