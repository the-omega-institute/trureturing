using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteComponentClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinate sphere bouquets, disjoint components, selected-vertex wedges, and complete finite-component joins.",
        H("Finite component models, vertex wedges, and joins"),
        Blocks(
            Node("sphere-model", "sphereComplex", "Native finite sphere models",
                "The zero-dimensional sphere is the complex of two distinct vertices. Higher sphere complexes are iterated simplicial joins with this two-point complex. Ghost ambient vertices are permitted; no unproved singleton face is added."),
            Node("sphere-homeomorphism", "sphereHomeomorph", "Actual Euclidean spheres",
                "For every natural dimension d, the coordinate realization of sphereComplex d is homeomorphic to the standard unit sphere in Euclidean space of dimension d+1. The base case is the explicit two-point homeomorphism; the induction uses the actual simplicial-join realization homeomorphism and the existing Euclidean sphere-join homeomorphism."),
            Node("bouquet-model", "bouquetComplex", "Finite positive-sphere bouquets",
                "A BouquetSpec is a finite list of positive sphere dimensions, counted with repetitions. Each native sphere is embedded with its selected vertex identified with one common coordinate vertex. The empty list is a single actual vertex and therefore one point component."),
            Node("bouquet-quotient", "bouquetQuotientHomeomorph", "The actual bouquet quotient",
                "The disjoint union of the finite sphere family and a separate common point, with precisely the repeated sphere basepoints and common point collapsed, is homeomorphic to the coordinate bouquet. The quotient kernel and surjectivity include the empty family."),
            Node("standard-bouquet", "standardBouquetHomeomorph", "Standard sphere quotient presentation",
                "The native finite bouquet is homeomorphic to the actual quotient bouquet of standard Euclidean spheres. Each sphere homeomorphism transports its specified basepoint, so this is an identification of actual quotient spaces."),
            Node("normal-model", "normalComplex", "All finite components",
                "The normal model is the tagged disjoint union of m coordinate bouquets. Different empty lists give different point components; no point component is deleted."),
            Node("normal-homeomorphism", "normalHomeomorph", "The tagged coproduct homeomorphism",
                "The coordinate realization of the normal complex is homeomorphic to the sigma type of its bouquet realizations, with their coproduct topology. The canonical normalPoint is the common vertex of the selected tagged bouquet."),
            Node("wplus", "WPlus", "Nonempty finite component homotopy types",
                "WPlus K means that the realization of K is homotopy equivalent to a normalComplex with a positive finite component count and a finite positive-sphere list for each component. Lists may be empty. This definition does not assert an arbitrary-index reduction."),
            Node("selected-specification", "selectedWedgeSpec", "Exactly the selected components merge",
                "For input counts m,n and selected indices i,j, the output has m+n-1 indices. It enumerates one bouquet with list p(i) concatenated with q(j), every p(k) with k different from i, and every q(l) with l different from j. The finite enumeration retains repetitions and empty lists."),
            Node("vertex-wedge", "vertexWedgeComplex", "The actual vertex gluing",
                "The ambient vertex set is the quotient of the tagged input vertex sets identifying exactly the two selected vertices. The face collection is the union of the mapped input face collections. Its realization is homeomorphic to the actual topological quotient wedge."),
            Node("closure-data", "SelectedVertexWedgeClosure", "Full based closure data",
                "The data contain positive input model counts, their bouquet specifications and selected indices, a separate BasedEquivalence from each original selected vertex to its model vertex, the based quotient-wedge normalization, an output component index, a direct WPlus witness, and a BasedEquivalence from the actual glued native vertex to that output normal vertex. BasedEquivalence contains continuous forward and backward maps, both strict basepoint equations, and both inverse homotopies relative to the corresponding singleton."),
            Node("selected-closure", "selectedVertexWedgeClosure", "Selected-vertex WPlus wedge closure",
                "For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. The cone-rebasing construction keeps the quotient map unchanged and changes its inverse by a native vertex-to-apex based equivalence. Its exact forward homotopy trace lies in the collapsed cone; composing the quotient with that trace is constant, which makes both concatenated inverse homotopies relative to the chosen vertex. Two such cone collapses on one native union yield the based auxiliary base-quotient splitting without assuming a quotient cylinder retraction. The selected-vertex wedge result is independent of the finite-component join result below. Arbitrary-index reduction and the graph-substitution conclusion are separate obligations and are not asserted here."),
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
