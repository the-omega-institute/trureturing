using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ComponentWeightedParityProductDocument : IScribeDocumentDefinition
{
    private const string Parent = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Parent + "Q9ComponentWeightedParityProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted parity row products in the nine-cube",
        H("Independent caps on the two parity sides"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-component-weighted-parity-row-product"),
                DeclarationHandle.Create(Module + ".sq_weight_le_parity_row_product_of_componentDefect_det_eq_zero"),
                H("A singular component defect forces a large parity row product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix an actual component of an induced subgraph of the nine-cube and a retained parity. For each vertex, sum the nonnegative direction weights over its neighbors on the opposite parity side of the component. If these sums are capped by r on the retained side and by s on the opposite side, where r and s are nonnegative, singularity of the weighted component defect forces the squared norm of the weight vector to be at most rs.")),
                    Paragraph(Text("The signed block and its transpose have infinity operator norms at most r and s, respectively. A nonzero kernel vector for the defect is an eigenvector of the block times its transpose with eigenvalue equal to the squared norm of the weights. Submultiplicativity bounds that eigenvalue by rs.")),
                    Paragraph(Text("Taking both caps equal to the larger side maximum recovers the common weighted row bound. Taking weights in {0,1} makes the weighted rows count active directions and makes the squared norm equal to the number of active axes. See "),
                        Ref(Parent + "Q9ComponentWeightedProfile.exists_weighted_row_of_componentDefect_det_eq_zero"),
                        Text(" and "), Ref(Parent + "Q9MaskedGram.componentDefect_mask_det_ne_zero"), Text(".")),
                    Paragraph(Text("For a cubic component, each parity side gives a family of direction triples. Take each cap to be the maximum weight sum over the triples on its side, with cap zero for an empty side. If their product lies below the squared norm, an actual component with those profiles has nonzero defect determinant at those weights. A 258-vertex induced subcubic support would have two distinct components for each retained parity whose defects are singular at every weighting, so each of those components must pass the product bound at every nonnegative weighting. See "),
                        Ref(Parent + "Q9ComponentSaturation.exists_two_weighted_singular_components"), Text(".")),
                    Paragraph(Text("An external integer calculation on the 22-type matching relaxation in weighted-parity-product-example.json gives 33 vertices on each side and 11 matching edges in each direction. For all 511 nonempty binary masks, the product of the two side maxima is at least the mask size. The weight vector (0,0,0,0,1,0,1,2,1) has even and odd maxima 2 and 3, so the product is 6 and the squared norm is 7. The square of the common maximum is 9 at that weight. These counts concern the matching relaxation. A cube embedding is outside the calculation.")),
                    Paragraph(Text("If both parity profiles use a fixed catalog of triples, let M be the largest weight sum of a catalog triple. For a nonzero weight, each side of a singular component must contain a triple whose weight sum times M is at least the squared norm. This gives a cut clause on each side. A coordinate permutation preserving the catalog also permutes the weights and preserves their squared norm, carrying clauses to clauses. An external integer enumeration on the 22-type catalog gives a stabilizer of order 32. Over the grid {0,1,2}⁹ it gives 132 inclusion-minimal side cuts that contain no binary-weight cut, in 13 orbits.")),
                    Paragraph(Text("These component certificates apply to candidate supports in Hong, Wu and Xia's open Problem 2, which asks whether the nine-cube admits a 258-vertex induced subgraph of maximum degree at most three. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
