using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9MaskedGramDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate masks for actual induced components",
        H("Active degrees and the 258-vertex obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-masked-gram-active-degrees"),
                DeclarationHandle.Create(Module + ".masked_gram_det_ne_zero"),
                H("Active degrees bound the rectangular Gram matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any row and column vertex sets, give the axes in a mask weight one and the remaining axes weight zero. If the row and column active-degree bounds have product smaller than the number of axes in the mask, subtracting the Gram matrix from the identity scaled by the mask size gives a nonsingular matrix.")),
                    Paragraph(Text("The maximum row and column sums of absolute entries bound the infinity operator norms of the signed block and its transpose. Their product bounds the Gram operator norm. A vector in the kernel of the shifted Gram would violate the strict norm bound unless it were zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-component-mask-determinant"),
                DeclarationHandle.Create(Module + ".componentDefect_mask_det_ne_zero"),
                H("An active-degree bound certifies an actual component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix any selected set, actual component and retained parity. Count masked neighbors across the two parity sides of that component. If the two uniform degree bounds have product smaller than the mask size, the component defect determinant is nonzero at the mask weights. The component decomposition gives the rectangular block, and the sum of squared mask weights is the mask size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-component-mask-exclusion"),
                DeclarationHandle.Create(Module + ".card_ne_258_of_component_mask_determinants"),
                H("Componentwise determinant certificates exclude size 258"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a parity in any induced subcubic support. If at most one actual component has zero defect determinant at every coordinate mask, the support cannot have size 258. A support of that size would have two distinct components singular at every real coordinate weighting, which includes every mask."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-component-degree-mask-exclusion"),
                DeclarationHandle.Create(Module + ".card_ne_258_of_component_degree_masks"),
                H("Componentwise active-degree certificates exclude size 258"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any induced subcubic support and fixed parity, size 258 is excluded if all but at most one actual component admit their own mask satisfying the active-degree product bound. For example, a component can use five active axes if each vertex has at most two neighbors along those axes.")),
                    Paragraph(Text("This condition can be used to exclude proposed supports for Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
