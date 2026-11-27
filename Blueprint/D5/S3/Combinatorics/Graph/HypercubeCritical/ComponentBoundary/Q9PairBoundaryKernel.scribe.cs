using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PairBoundaryKernelDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "Q9PairBoundaryKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-axis reduction of weighted Huang boundary kernels",
        H("Eliminating the empty slice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q-nine-pair-boundary-kernel"),
                DeclarationHandle.Create(Module + ".weightedBoundaryKernelEquiv"),
                H("The two-slice kernel of the nine-cube action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Order the blocks by their leading bits as 00, 10, 01, 11. "
                        + "The allowed source blocks are M, S, S, and the empty set. "
                        + "The allowed image blocks are independently M', S', S', and the empty set. "
                        + "A boundary kernel consists of functions supported on the source mask "
                        + "whose weighted Huang images are supported on the image mask.")),
                    Paragraph(Text(
                        "Let a and b be the leading weights, let B be the weighted action "
                        + "of the seven remaining axes, and put c = a² + b². Over a field "
                        + "with c nonzero, the empty source block forces f11 = 0. "
                        + "The empty image block then forces b f10 + a f01 = 0. "
                        + "Thus p = f00 and q = (a f10 - b f01) / c recover the source as "
                        + "(p, a q, -b q, 0).")),
                    Paragraph(Text(
                        "In these coordinates the weighted Huang action sends (p, q) to "
                        + "(B p + c q, -B q + p). The lift preserves and reflects the "
                        + "paired masks on both sides, giving a linear equivalence of "
                        + "the two boundary kernels.")),
                    Paragraph(Text(
                        "If the field contains r with r² = c, rescale q to r q. "
                        + "The action in the rescaled coordinates is the weighted Huang "
                        + "action with a single leading axis of weight r. The positive B "
                        + "slice has leading bit true."))),
                DescribeRole.Definition)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9IsotropicHuang")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9WeightedStarLift"))
        ]));
}
