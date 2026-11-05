using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class SelectedWedgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure/SelectedWedge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinate sphere bouquets close under gluing any existing selected vertices, with both inverse homotopies relative to the corresponding singleton.",
        H("SelectedWedge"),
        Blocks(
            Paragraph(Text("Finite coordinate sphere bouquets close under gluing any existing selected vertices, with both inverse homotopies relative to the corresponding singleton.")),
            Node("selected-specification", "selectedWedgeSpec", "Exactly the selected components merge",
                "For input counts m,n and selected indices i,j, the output has m+n-1 indices. It enumerates one bouquet with list p(i) concatenated with q(j), every p(k) with k different from i, and every q(l) with l different from j. The finite enumeration retains repetitions and empty lists."),
            Node("vertex-wedge", "vertexWedgeComplex", "The actual vertex gluing",
                "The ambient vertex set is the quotient of the tagged input vertex sets identifying exactly the two selected vertices. The face collection is the union of the mapped input face collections. Its realization is homeomorphic to the actual topological quotient wedge."),
            Node("closure-data", "SelectedVertexWedgeClosure", "Full based closure data",
                "The data contain positive input model counts, their bouquet specifications and selected indices, a separate BasedEquivalence from each original selected vertex to its model vertex, the based quotient-wedge normalization, an output component index, a direct WPlus witness, and a BasedEquivalence from the actual glued native vertex to that output normal vertex. BasedEquivalence contains continuous forward and backward maps, both strict basepoint equations, and both inverse homotopies relative to the corresponding singleton."),
            Node("selected-closure", "selectedVertexWedgeClosure", "Selected-vertex WPlus wedge closure",
                "For finite pre-abstract simplicial complexes K,L satisfying WPlus, and any existing selected vertices a,b, construct SelectedVertexWedgeClosure K L a ha b hb. Normalize the input vertices using the two actual native singleton-cylinder retractions, replace both arms by their based packets, and rearrange the quotient into the selected concatenated bouquet and every unselected component. The component count is m+n-1. Finally use based_inverse only between native finite realizations to obtain both relative inverse homotopies at actual vertices. No cylinder retraction on an arbitrary quotient is assumed. This is a classical finite wedge closure ingredient for Carnero Bravo, arXiv:2505.06457v2, Question 22. The cone-rebasing construction keeps the quotient map unchanged and changes its inverse by a native vertex-to-apex based equivalence. Its exact forward homotopy trace lies in the collapsed cone; composing the quotient with that trace is constant, which makes both concatenated inverse homotopies relative to the chosen vertex. Two such cone collapses on one native union yield the based auxiliary base-quotient splitting without assuming a quotient cylinder retraction. The selected-vertex wedge result is independent of the finite-component join result below. Arbitrary-index reduction and the graph-substitution conclusion are separate obligations and are not asserted here."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
