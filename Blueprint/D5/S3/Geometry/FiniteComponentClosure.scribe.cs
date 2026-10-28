using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteComponentClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinate sphere bouquets, disjoint components, and selected-vertex wedge closure.",
        H("Finite component models and vertex wedges"),
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
                "For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. Complete finite-component join closure, arbitrary-index reduction, and the graph-substitution conclusion are separate obligations and are not asserted here."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
