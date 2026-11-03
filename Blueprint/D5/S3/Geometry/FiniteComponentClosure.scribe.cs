using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteComponentClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite-component ordinary and native joins preserve every sphere-pair, suspension, and circle term, including point components. Empty whole factors are treated separately.",
        H("Finite component join closure"),
        Blocks(
            Paragraph(Text("Complete finite-component ordinary and native joins preserve every sphere-pair, suspension, and circle term, including point components. Empty whole factors are treated separately.")),
            Node("join-dimensions", "finiteJoinSpec", "Every join term and multiplicity",
                "For positive component counts m,n, the dimension list concatenates the p+q+1 terms over every pair of components and every occurrence of a sphere in their lists; n-1 copies of each left p+1 suspension term; m-1 copies of each right q+1 suspension term; and (m-1)(n-1) copies of dimension one. Empty lists are actual point components and remain in the component count. Sphere occurrences and repeated dimensions retain their multiplicities. The all-point case m=n=2 therefore produces one circle."),
            Node("join-closure-data", "FiniteComponentJoinClosure", "Both carriers and all relative homotopies",
                "The closure data contain the positive input component counts and finite lists, their actual normalizing homotopy equivalences, the actual native join equivalence to the single output bouquet specified by finiteJoinSpec, and the actual ordinary quotient join equivalence. At every source native vertex, the data include continuous maps and inverses, both strict basepoint equations, and both inverse homotopies relative to the source and target singleton. The ordinary join receives the same full based packet at the inverse image of that vertex under the simplicial-join realization homeomorphism. A direct WPlus witness is also retained."),
            Node("join-closure", "finiteComponentJoinClosure", "Complete finite-component WPlus join closure",
                "For finite pre-abstract simplicial complexes K,L satisfying WPlus, construct FiniteComponentJoinClosure K L. A cone collapse is rebased at a native cone vertex while preserving its original quotient map: the exact native homotopy trace remains in the collapsed cone, so both inverse homotopies fix the chosen point. Two such collapses on one native union give the based auxiliary split. The cone modulo its base is identified by an actual homeomorphism with a native suspension, with its base class mapped to the actual north-pole vertex. Iterating the two-component split contributes one suspension per extra component; decomposing the suspension of a disconnected input contributes the circle terms. Native common-vertex distribution normalizes bouquet joins, using the existing actual Euclidean sphere-join homeomorphism for every natural pair of dimensions, including S0. The empty bouquet remains a point and its join is contracted as an actual cone. Reindexing through finite dimension fibers preserves every sphere occurrence and puts the output in the four-block order of finiteJoinSpec. Every further basepoint adjustment uses native finite vertex cylinders or an already constructed native based presentation. No quotient HEP or arbitrary quotient cylinder is assumed. This is the finite closure ingredient of Carnero Bravo, arXiv:2505.06457v2, Question 22, and does not prove the full graph-substitution question."),
            Node("empty-left-join", "ordinaryJoinEmptyLeft", "Empty whole left factor",
                "For arbitrary topological spaces X,Y, IsEmpty X produces an elimination map from the actual ordinary join quotient of X and Y to the empty type. This branch concerns an empty whole factor, separately from a nonempty point bouquet or the augmented simplicial join convention."),
            Node("empty-right-join", "ordinaryJoinEmptyRight", "Empty whole right factor",
                "For arbitrary topological spaces X,Y, IsEmpty Y produces an elimination map from the actual ordinary join quotient of X and Y to the empty type. No point is inserted into an empty ordinary join."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
