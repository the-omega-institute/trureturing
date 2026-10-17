using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class ZeroTraceHullDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite convex hull meets a family of nonpositive supports at the hull of its zero-support vertices.",
        H("Convex hull of a common supporting trace"),
        Blocks(
            Paragraph(Text("Let s be a set of points in the four-coordinate real space and let L be a family of linear supports. "
                + "Assume every generator is in every nonpositive support halfspace. The points of the convex hull on the common zero trace "
                + "are exactly the convex hull of those generators that already lie on every zero trace.")),
            Describe.Lean(
                DescribeId.Create("zero-trace-hull"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull"),
                H("A common zero trace commutes with convex hull"),
                StatementSource.FromAuthor(F.Disp(F.Id("zeroTraceHull"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The forward inclusion follows from convexity of the hull and linearity of each support. "
                        + "For the reverse inclusion, write a point of the hull as a finite convex combination. "
                        + "Each summand is nonpositive, while the weighted sum is zero, so every nonzero-weight summand has zero support. "
                        + "Filtering out zero weights preserves both the total weight and the represented point."))),
                DescribeRole.Theorem))));
}
