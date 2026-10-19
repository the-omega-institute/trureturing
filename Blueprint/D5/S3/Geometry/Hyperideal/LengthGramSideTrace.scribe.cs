using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramSideTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common zero trace of a side support and a cyclic edge support is the original closed edge segment.",
        H("A cyclic side trace is an original edge segment"),
        Blocks(
            Paragraph(Text("Fix six strictly positive lengths in the original order 01, 02, 03, 23, 13, 12. "
                + "For a side label k, the side support is the coordinate support x_k=0. "
                + "The six cyclic supports are the alternating coordinate and Gram-row supports of the three remaining labels.")),
            Describe.Lean(
                DescribeId.Create("cycle-edge-hull"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull"),
                H("Two supporting traces recover the corresponding closed edge"),
                StatementSource.FromAuthor(F.Disp(F.Id("cycleEdgeHull"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The endpoint support classification identifies exactly two original ordered endpoints "
                        + "on the simultaneous zero trace. The common zero-trace convex-hull lemma then identifies "
                        + "the whole intersection with their convex hull, which is the displayed closed segment. "
                        + "The result concerns the original coefficient body and its original endpoint coordinates."))),
                DescribeRole.Theorem))));
}
