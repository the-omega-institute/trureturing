using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9LaurentGainPartitionDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Boundary = Cube + "ComponentBoundary/";
    private const string Owner = Boundary + "Q9LaurentGainPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laurent coefficients determine the direction partition of a cubic support in Q9",
        H("The direction partition from a positive Laurent identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-positive-evaluation-determines-laurent-identity"),
                DeclarationHandle.Create(Owner + "laurentIdentity_iff_evaluateLaurent"),
                H("Positive real weights determine the Laurent row identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Equality of the Laurent sums at every strictly positive weight vector is equivalent to equality of their coefficients. Shift both finite exponent sets by the same vector to obtain ordinary polynomials. Polynomial uniqueness on a product of infinite sets recovers equality after the shift, and subtracting the shift recovers the original exponent multiplicities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-laurent-two-step-gain"),
                DeclarationHandle.Create(Owner + "path_exponent_and_gain"),
                H("Reversing a two-step path determines the matched axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume the Laurent identity at every selected vertex of one parity. The row has one monomial for each directed internal two-step path that does not backtrack. The coefficient of an exponent counts all paths with that exponent. On the other side of the identity, each missing direction contributes its square once.")),
                    Paragraph(Text("For a path with axes i and j, add the forward and reverse exponent equations. The potential differences cancel. The two square axes must then be i and j, and the forward square cannot use the internal first axis i. It uses j, which gives the gain e_j − e_i."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-laurent-direction-partition"),
                DeclarationHandle.Create(Owner + "neighbor_triples_partition"),
                H("The internal direction triples of the three neighbors partition the axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each selected vertex of that same parity, each missing axis appears in exactly one two-step path because its square coefficient is one. Each internal axis appears at exactly the neighbor across that axis, where it is the returning direction. Cubicity makes the resulting three sets triples.")),
                    Paragraph(Text("Where the weighted Huang kernel yields this Laurent identity, the two theorems give necessary local constraints on the support. The support size question is Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9IsotropicHuang")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9PureExteriorLink"))
        ]));
}
