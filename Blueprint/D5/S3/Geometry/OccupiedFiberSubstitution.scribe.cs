using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class OccupiedFiberSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OccupiedFiberSubstitution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induced heterogeneous substitutions retain precisely the occupied base and selected fibers.",
        H("Occupied-fiber substitution"),
        Blocks(
            Node("occupied-base", "occupiedBase", "The occupied base",
                "For a dependent family D over V and any subset T of its sigma type, U consists of exactly those v for which some pair (v,d) lies in T. Empty fibers contribute no occupied base vertices.", DescribeRole.Definition),
            Node("selected-fiber", "selectedFiber", "The selected fiber",
                "For u in U, the selected fiber consists of d in D(u) for which (u,d) lies in T, with the actual membership proof retained.", DescribeRole.Definition),
            Node("selected-fiber-nonempty", "selectedFiberNonempty", "Nonempty occupied fibers",
                "The witness defining membership in U supplies a selected fiber vertex. This needs no global assumption that T is nonempty.", DescribeRole.Definition),
            Node("vertex-equivalence", "vertexEquiv", "Mutually inverse vertex maps",
                "A vertex ((v,d),h) of T maps to ((v, exists d with h),(d,h)). The inverse forgets the occupied-base proof and returns ((v,d),h). The first composite is the identity on T, and the second is the identity on the dependent sum of selected fibers by proof irrelevance. These formulas also apply when T is empty.", DescribeRole.Definition),
            Node("selected-graph", "selectedGraph", "The actual restricted substitution",
                "Induce G on U, induce each H(u) on the selected d, and form their heterogeneous substitution. Neither source class assumptions nor closure assumptions occur.", DescribeRole.Definition),
            Node("adjacency", "adjacency_iff", "Exact adjacency transport",
                "For arbitrary V, dependent fibers D, simple graphs G and H(u), any selected set T and x,y in T, adjacency in the induced original substitution holds if and only if adjacency holds between their split vertices in the selected graph. A base edge remains the same induced base edge. A within-fiber edge keeps its actual endpoints and membership proofs in the induced fiber graph. Conversely each of these two kinds of selected edge forgets to the corresponding original edge.", DescribeRole.Theorem),
            Node("graph-isomorphism", "graphIso", "The occupied-fiber graph isomorphism",
                "The explicit mutually inverse vertex maps and the proved adjacency equivalence give an actual graph isomorphism from the original substitution induced on T to the substitution of selected induced fibers over U.", DescribeRole.Definition),
            Node("independent-faces", "mapped_independence_faces", "Equality of mapped independent-face complexes",
                "For finite V and finite dependent fibers D(u), with decidable equality, and arbitrary G,H,T, map the nonempty independent faces of the induced original substitution along the graph isomorphism. The result is exactly the nonempty independent-face complex of the selected graph. In the forward direction, adjacency reflection preserves independence. In the reverse direction, image under the inverse vertex equivalence recovers every selected independent face, and adjacency preservation proves independence of its preimage. Nonemptiness is transported by finite-set image in both directions.", DescribeRole.Theorem),
            Node("independence-homeomorphism", "independenceHomeomorph", "Homeomorphism of the actual independence realizations",
                "For every finite base V, finite dependent fibers D(u), simple graphs G and H(u), and arbitrary T in the sigma vertex set, the native finite-coordinate realization of the independence complex of the original substitution induced on T is homeomorphic to that of the selected substitution over U. Apply the existing embedding realization homeomorphism to the explicit graph isomorphism, then transport along the proved equality of mapped independent-face complexes. The adjacency result is thus used in the realization transport. No second coordinate transport construction is needed. Empty T and empty original fibers remain in scope. This exact heterogeneous transport is a local RepoDerived refinement associated with the induced-subgraph description in Carnero Bravo arXiv:2505.06457v2, not an exact theorem attributed to the paper. It supplies an intermediate step for the unsuspended hereditary induction and asserts neither Question 22 nor membership in the stronger SW class.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
