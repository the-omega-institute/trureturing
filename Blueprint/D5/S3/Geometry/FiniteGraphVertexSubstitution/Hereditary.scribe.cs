using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGraphVertexSubstitution;

internal sealed class HereditaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual mixed graph stages and original hereditary substitution induction.",
        H("Hereditary graph substitution"),
        Blocks(
            Node("stage-fiber", "stageFiber", "The actual mixed replacement family",
                "At a vertex in the replaced finset use its final fiber D(v); elsewhere use PUnit in the same fiber universe. This family retains all previously replaced fibers on every restricted current link.", DescribeRole.Definition),
            Node("stage-finite", "stageFiberFintype", "Finiteness of the mixed fibers",
                "Each mixed fiber is finite by its selected finite final-fiber or singleton branch.", DescribeRole.Definition),
            Node("stage-decidable", "stageFiberDecidableEq", "Decidable equality of the mixed fibers",
                "Branch reduction transfers decidable equality from each final fiber or from the singleton.", DescribeRole.Definition),
            Node("stage-nonempty", "stageFiberNonempty", "Nonempty mixed fibers",
                "If every final fiber is nonempty, both branches of every mixed fiber are nonempty. This supplies actual current-link vertices when the restricted base is nonempty.", DescribeRole.Definition),
            Node("stage-graphs", "stageGraphs", "Graphs on the mixed family",
                "Transport H(v) across the selected branch equality, and transport the edge-free singleton graph across the other branch equality. These are graphs on the actual dependent stage types.", DescribeRole.Definition),
            Node("initial-stage", "initialStageIso", "The initial stage is the base graph",
                "The stage with no replaced vertices is isomorphic to the base graph, by fiberwise singleton transport and projection. This starts replacement induction without an order-two assumption.", DescribeRole.Definition),
            Node("final-stage", "finalStageIso", "The final stage is full substitution",
                "The stage indexed by the full base finset is isomorphic to the full original heterogeneous substitution, by the explicit selected-fiber equivalences.", DescribeRole.Definition),
            Node("replacement-stage", "replacementStageIso", "A supplier replacement is the next mixed stage",
                "Pointwise branch casts identify the supplier newFiber construction at v with the stage indexed by insert v R, preserving actual fiber adjacency. When v is absent from R, the old stage fiber at v is a singleton; no singleton assumption is made on the new final fiber. These transports serve the original private hereditarySubstitutionCore, with strong induction on base cardinality and inner induction on replaced vertices. The link carries all current mixed fibers. A nonempty link uses the smaller-base induction; an empty link uses the augmented simplicial unit. The core is consumed directly by HereditaryLexicographicProduct with the class of actual finite positive sphere-bouquet models. There its point and homotopy inputs are constructed, and its finite native ordinary-join and selected-coordinate-vertex wedge inputs are discharged by the actual FiniteComponentClosure constructions. No second graph induction is introduced. The original core alone remains conditional on its explicit class-closure inputs.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
