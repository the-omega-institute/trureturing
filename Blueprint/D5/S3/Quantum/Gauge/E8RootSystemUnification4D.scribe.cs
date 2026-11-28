using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class E8RootSystemUnification4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/E8RootSystemUnification4D.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/LieTheory/viazovska2017eightdimensionalpacking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "E8 roots and the exceptional family branching.",
        H("E8 roots and the exceptional family branching"),
        Blocks(
            Paragraph(Text("All root vectors use the same eight real coordinates as the existing E6 subsystem. The doubled integral model makes parity, Weyl reflections and simple-root coefficients exact. The branching records the adjoint root sets and their weights with respect to E6 and the orthogonal family A2.")),
            Entry("e8roots-card", "e8Roots_card", "The 240 exceptional roots",
                "The doubled integral construction has 112 two-coordinate roots with entries of magnitude two and 128 sign vectors with even minus parity. Their disjoint union has cardinality 240."),
            Entry("e8-lie-algebra-dimension", "e8_lie_algebra_dimension", "Adjoint dimension count",
                "The rank-eight Cartan contribution and the 240 roots give dimension 248."),
            Entry("e8roots-simply-laced", "e8Roots_simply_laced", "Root square length",
                "Every root has Euclidean square length two after dividing the integral coordinates by two."),
            Entry("e8roots-crystallographic-inner-products", "e8Roots_crystallographic_inner_products", "Crystallographic inner products",
                "Two roots have inner product in the set consisting of minus two, minus one, zero, one and two. The upper endpoint characterizes equal roots and the lower endpoint characterizes opposite roots."),
            Entry("e8roots-weyl-reflection-closed", "e8Roots_weyl_reflection_closed", "Weyl reflections and negation",
                "For roots alpha and beta, subtracting the inner product of alpha and beta times alpha from beta gives a root. The negative of alpha is also a root."),
            Entry("e8-dynkin-simple-roots", "e8_dynkin_simple_roots", "Unimodular simple system",
                "The eight explicit simple roots belong to the root set and extend the six simple roots of E6. Their Gram matrix is the integral Cartan matrix and has determinant one. They are linearly independent, and every root has integral coordinates in this basis with all coefficients nonnegative or all nonpositive."),
            Entry("e6-and-a2-subsystems-in-e8", "e6_and_a2_subsystems_in_e8", "Orthogonal exceptional and family subsystems",
                "The E6 and A2 root sets lie in E8. The A2 roots are exactly the six E8 roots orthogonal to the E6 subspace. Its two simple roots span that orthogonal complement and have Gram matrix with diagonal two, off-diagonal minus one and determinant three. Every E6 root is orthogonal to every A2 root."),
            Entry("e8-e6-x-su3-branching-248", "e8_e6_x_su3_branching_248", "Four branches of the adjoint root set",
                "The four pairwise disjoint branches cover the E8 roots and have sizes 72, 6, 81 and 81. The first two branches contribute six and two Cartan directions respectively, giving the adjoint dimension count 78 plus 8 plus 81 plus 81."),
            Entry("e8-family-weight-fibers", "e8_family_weight_fibers", "Fundamental and conjugate weight fibers",
                "The three fundamental weights are (1, 0), (-1, 1) and (0, -1) in simple-root inner product coordinates. The conjugate weights are their negatives. The fibers consist precisely of the E8 roots with the specified weight, and each fiber has 27 elements. The three fibers partition each 81-root branch."),
            Entry("e8-e6-generation-weights", "e8_e6_generation_weights", "SO(10) and abelian charges in each fiber",
                "Each fundamental fiber is in bijection with the E6 basis of 27 states. The bijection preserves the five-coordinate SO(10) Cartan evaluation and the abelian charge. The charge sectors at 1, minus 2 and 4 have sizes 16, 10 and 1 respectively."),
            Entry("e8-family-root-steps", "e8_family_root_steps", "Lowering between the three family weights",
                "For each of the 27 states, subtracting the first A2 simple root reaches the second fiber. Subtracting the second A2 simple root from there reaches the third fiber."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
