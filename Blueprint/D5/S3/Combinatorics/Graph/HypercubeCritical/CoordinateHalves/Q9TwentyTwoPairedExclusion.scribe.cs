using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9TwentyTwoPairedExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9TwentyTwoPairedExclusion", H("Exclusion of a 22-vertex half in the nine-cube"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-no-twenty-two-half"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half"),
            H("An order-72 balanced cubic support has no 22-vertex half"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Suppressing the degree-two vertices yields a finite list of compressed halves. "
                    + "The singleton parity cases are incompatible with an opposite half of size fifty.")),
                Paragraph(Text("The remaining compression consists of two complete bipartite graphs on parts of sizes "
                    + "two and three, with the three terminals matched. Translate the root and permute the axes "
                    + "to obtain two possible seeds, indexed by whether the second axes of the root paths coincide.")),
                Paragraph(Text("For every compatible placement of the subdivisions, parity recovers the opposite "
                    + "half and forces a vertex of degree greater than three. This excludes the 22/50 cut in the "
                    + "order-72 component case of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))]));
}
