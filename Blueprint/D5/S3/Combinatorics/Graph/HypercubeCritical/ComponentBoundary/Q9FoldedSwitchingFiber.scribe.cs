using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FoldedSwitchingFiberDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSwitchingFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity and frozen edges jointly determine the affine family for exact signed rows.",
        H("Joint switching fibers for folded signed rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-switching-fiber"),
                DeclarationHandle.Create(Module + ".joint_switching_fiber"),
                H("Joint compatibility, dimension and exact signed rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On the actual edges of a finite simple graph, let B be the binary incidence matrix, T its transpose, and P the restriction to the specified edges. The map J combines B and P. For original edge bits s, the joint target b combines the integer degree targets q reduced modulo two with the specified bits f. The family W consists of vertex switches s + Tz with J(s + Tz) = b.")),
                    Paragraph(Text("The family is nonempty precisely when b − Js belongs to the image of JT. For each reference w₀ in W, an edge vector w belongs to W precisely when w = w₀ + d for some d in D = ker J ∩ im T. Subtracting two switches cancels their common joint target. Adding any direction in D preserves the target and lifts to a change of vertex labels.")),
                    Paragraph(Text("The dimension of D plus the rank of JT equals the rank of B, by restricting J to the image of T and applying rank–nullity. Let S = ker J, regarded as a subspace of the original cycle space, and let R be the original quotient by the bicycle space restricted to S. Its kernel corresponds to D, so dim D + rank R = dim S. Both computations use the cut space of the original graph.")),
                    Paragraph(Text("If every ordinary q-factor has the specified bits f, exact switched signed rows of degree minus 2q exist precisely when W contains a q-factor. The integer negative degrees of an exact signing reduce to the prescribed parity, and the frozen bits follow from the q-factor hypothesis. The test on W uses the full integer degrees."))),
                DescribeRole.Theorem),
            Paragraph(Text("The archived induced Q₄ fixture on vertices 0, 1, 6, 7, 8, 10, 11, 12, 14 and 15 has two ordinary q-factors and two globally parity-compatible Huang signings. Each frozen edge bit occurs in at least one of those signings. Rows 10 and 15 together have prescribed parity one, and the common q-factor bits at (7,15) and (8,10) have sum one. Adding these constraints cancels the two off-square edges and forces parity zero on 10–11–15–14–10. The Huang signing has parity one on that square, and a vertex switch preserves its parity. The joint system is therefore inconsistent. The fixture and its checks are recorded in order126/joint-frozen-huang-square.json.")),
            Paragraph(Text("In the nine archived order-126 Huang folds, the joint fiber dimensions range from one to seven, giving two to 128 parity-compatible signings with the prescribed bits. Each of those nine fibers contains two exact signings, as recorded in order126/frozen-edge-switching-fiber.json. The two folds of ambient quotient rank 14 both have fiber dimension one, while the images of their supported cycle spaces have dimensions one and 14 respectively. A separate archived rank-24 fold of the block72 example has a four-dimensional image of supported cycles, with disjoint components contributing lines and an exact exchange attaining the target. These are readings for the recorded folds. The value of f₂(Q₉) remains the question in Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        []));
}
