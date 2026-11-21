using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class BinaryQuadraticMomentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic moments of binary cube supports",
        H("Quadratic moments of binary cube supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-cube-quadratic-pair-moment"),
                DeclarationHandle.Create(Module + ".pairMoment"),
                H("Pair moments of a cube word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct coordinates the pair moment sums the word over the vertices where both coordinates equal one. The diagonal is set to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-cube-quadratic-moment-potentials"),
                DeclarationHandle.Create(Module + ".exists_pairMoment_eq_add"),
                H("Coordinate potentials for the pair moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In odd dimension the pair moments of a binary adjacency fixed word are sums of one potential per coordinate. Each coordinate flip is an involution, so cube adjacency is self-adjoint. The coordinate contraction writes any fixed word as the image of adjacency plus the identity. Pairing against another fixed word therefore gives zero. On a triangle the sum of the three pair monomials is fixed because every linear correction from the coordinate flips occurs twice. The triangle equations recover all pair moments from the moments at one base coordinate.")),
                    Paragraph(Text("For a Huang-saturated cubic support, reducing the unit signed eigenrow equation modulo two gives a fixed binary indicator. In Hong, Wu and Xia's nine-cube problem, the 36 off-diagonal moments are determined by the eight moments at a chosen base coordinate. This supplies 28 linear parity equations on candidate supports. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
