using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedSwapNormalFormDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Boundary = Cube + "ComponentBoundary/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal form for a balanced nine-cube support under a leading swap",
        H("The two fixed corner fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q-nine-leading-swap-normal-form"),
                DeclarationHandle.Create(Boundary + "Q9SignedSwapNormalForm.exists_cubeMask_of_leadingSwap"),
                H("One fixed corner fibre is empty"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The gauge for the pure transposition of the first two coordinates "
                        + "is −1 on the 00 fibre and +1 elsewhere. On a balanced support "
                        + "invariant under the swap, multiply this gauge by the switching signs "
                        + "at a vertex and its swapped vertex. The resulting sign is constant "
                        + "on each induced component.")),
                    Paragraph(Text(
                        "On a nonempty preconnected support, this constant is the sign of the generator "
                        + "of the two-element swap group acting on the switching function. "
                        + "At a fixed vertex the switching signs square to 1. Occupied 00 and 11 "
                        + "fibres would then force the same sign to be both −1 and +1.")),
                    Paragraph(Text(
                        "Complement both leading coordinates if 00 was omitted and use the "
                        + "identity otherwise. The omitted fibre becomes 11, the swap equates "
                        + "the two mixed fibres, and signed cube covariance preserves balance. "
                        + "The resulting support has slices (M, S, S, ∅) in order 00, 10, 01, 11."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Cube + "HuangCubeCovariance")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9PairBoundaryKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9IsotropicHuang"))
        ]));
}
