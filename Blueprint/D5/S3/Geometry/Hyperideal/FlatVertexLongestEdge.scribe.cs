using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FlatVertexLongestEdgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A flat hyperbolic face angle forces the opposite truncated edge to be longest.",
        H("Flat hyperbolic vertex edge inequality"),
        Blocks(
            Paragraph(Text(
                "For positive real side lengths a, b and c, define the hyperbolic cosine-law "
                    + "quantity (cosh(a) cosh(b) - cosh(c)) / (sinh(a) sinh(b)). If this quantity "
                    + "is at most -1, then a+b is at most c. This is the reusable analytic core "
                    + "of the flat-vertex longest-edge argument; it does not construct the surrounding "
                    + "hyperideal face, identify an arcosh truncation, or prove the global CFMP geometry.")),
            Describe.Lean(
                DescribeId.Create("flat-vertex-face-cosine"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.faceCosine"),
                H("Hyperbolic face cosine-law quantity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient of cosh(a) cosh(b) - cosh(c) by the positive denominator "
                        + "sinh(a) sinh(b)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("flat-vertex-longest-edge"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.flat_vertex_longest_edge"),
                H("Flat angle makes the opposite side longest"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive a, b and c, the hypothesis faceCosine(a,b,c) <= -1 implies "
                        + "a+b <= c. The proof uses positivity of sinh on positive inputs, the "
                        + "addition formula for cosh, and injectivity of cosh on nonnegative reals."))),
                DescribeRole.Theorem))));
}
