using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphSubgraphSuspensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSubgraphSuspension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local arbitrary-subgraph transport and the actual reduced singular integral homology endpoint.",
        H("Local subgraphs and homology endpoint"),
        Blocks(
            Node("localmaxequiv", "localMaxEquiv", "Local and spanning maximal sets",
                "For every subgraph H of G, restriction to H.verts bijects maximal independent sets of the spanning graph with those of the local graph. The inverse adjoins all outside vertices, which are isolated in the spanning graph.", DescribeRole.Definition),
            Node("localsuspensiongraph", "localSuspensionGraph", "The local vertex convention",
                "The literal local gadget keeps old vertices of G and retains every G-edge absent from H. An apex indexed by a maximal independent set of the local H-graph is adjacent to exactly its complement inside H.verts, together with the hub. No induced-subgraph assumption is imposed.", DescribeRole.Definition),
            Node("spanninglocaliso", "spanningLocalIso", "Exact gadget identification",
                "For every subgraph H of G, the maximal-independent-set bijection gives a graph isomorphism between the spanning and local gadgets. It fixes all old vertices and the hub and preserves all retained G-edges.", DescribeRole.Definition),
            Node("reducedhomologyiso", "reducedHomologyIso", "The integral singular homology shift",
                "For every nonempty finite vertex type V, every pair of simple graphs H less than or equal to G on V, and every natural q at least one, the actual reduced singular homology with integral coefficients of the gadget independence realization in degree q+1 is isomorphic to that of the actual G-independence realization in degree q. The proof applies the existing open-cover reduced Mayer-Vietoris connecting isomorphism to U and O, then homotopy invariance to the constructed intersection equivalence. It assumes no homology shift, homotopy equivalence, retraction or quasi-isomorphism.", DescribeRole.Definition),
            Node("subgraphreducedhomologyiso", "subgraphReducedHomologyIso", "Arbitrary Mathlib subgraphs",
                "For every nonempty finite G, every possibly noninduced Mathlib subgraph H of G, and every q at least one, the spanning version of the literal gadget shifts the actual reduced singular integral homology by one degree.", DescribeRole.Definition),
            Node("localsubgraphreducedhomologyiso", "localSubgraphReducedHomologyIso", "The local gadget homology shift",
                "For every nonempty finite G, every arbitrary possibly noninduced subgraph H, every finite instance on H.verts, and every natural q at least one, the actual local gadget independence realization in degree q+1 has reduced singular integral homology isomorphic to that of G in degree q. Transport uses the proved graph isomorphism and the existing coordinate homeomorphism. These results provide core machinery for Carnero Bravo Question 32. They do not settle its hereditary SW statement for all induced subgraphs and arbitrary m; Question 35 about the full rectangle is different. Seed comparison, complete gadget replay, king rotation and the sphere-bouquet torsion obstruction are further obligations. The graph suspension and star-cluster mechanisms belong to the work of Adamaszek, Barmak and Csorba; the explicit coordinate neighborhoods are the construction described here, without a priority claim.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
