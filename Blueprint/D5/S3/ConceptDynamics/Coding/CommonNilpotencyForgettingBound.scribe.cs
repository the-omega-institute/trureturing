using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CommonNilpotencyForgettingBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiber differences detect exact path forgetting with a finite dimension stopping bound.",
        H("Exact forgetting and common nilpotency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-nilpotency-forgetting-bound"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CommonNilpotencyForgettingBound.common_nilpotency_forgetting_bound"),
                H("Faithful linearization and the dimension stopping bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let Q be a finite set of states with a surjection onto the n vertices of a finite directed multigraph. Every numbered edge has a predecessor function from its terminal fiber to its initial fiber. A compatible path acts by composing these functions in path order. Forgetting at length d means that every length-d path function is constant on its entire terminal fiber, including the identity functions at length zero.")),
                    Paragraph(Text("In the rational free vector space on Q, let D be the span of differences of basis vectors in the same fiber. This is exactly the kernel of coefficient aggregation onto the vertices: coefficients sum to zero separately in each fiber. Its dimension is the cardinality of Q minus n. Extend each predecessor function linearly on its terminal fiber and by zero on the other fibers. The resulting edge maps preserve D. Their restrictions to D are the operators considered here.")),
                    Paragraph(Text("Every incompatible numbered edge word has zero linear product. For each natural d, all compatible paths of length d forget the terminal state if and only if every ordered length-d product has zero image on D. This criterion concerns every product individually. It does not replace the family by the power of a sum or average.")),
                    Paragraph(Text("Start with W at zero equal to D, and obtain the next W by summing all edge-map images of the preceding W. At each depth j, W is the sum of the images of all ordered products of length j. These subspaces decrease. Equality of two adjacent terms forces equality at every subsequent depth.")),
                    Paragraph(Text("Forgetting at depth d is equivalent to W at d being zero, so the sets of forgetting depths and zero-image depths have exactly the same least element whenever they are nonempty. If finite forgetting exists, this least depth is at most the dimension of D, namely the cardinality of Q minus n. Equivalently, finite forgetting exists exactly when W at that bound is zero. This is a finite test with rational linear algebra, and includes D equal to zero with least depth zero.")),
                    Paragraph(Text("A choice of one representative in each fiber expresses every vector with zero fiber sums as a sum of state differences. On a compatible path, each such difference maps to the difference of its two actual lifted states; distinct basis vectors remain distinct. Induction identifies all product images with the recursive image sums. Before the first zero term, any equality would force permanent stability, so every step strictly lowers dimension. Essentiality of the graph is unnecessary for these conclusions."))),
                DescribeRole.Theorem))));
}
