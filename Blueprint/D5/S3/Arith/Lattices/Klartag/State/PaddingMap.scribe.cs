using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class PaddingMapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/PaddingMap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Padding Map"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate padding map to the stochastic ellipsoid construction.")),
            Node("claim-2", "norm_padUnit", "norm pad Unit",
                "The padding direction is a unit vector. w is the projected drift direction π_k v_k, e a fresh direction orthogonal to it; √(1 − ‖w‖²) is Klartag's padding amplitude, and the Pythagorean identity is exactly the statement that the padded conditional variance is h.", DescribeRole.Theorem),
            Node("claim-3", "map_scaled_inner", "map scaled inner",
                "The padded increment's law at a *fixed* unit direction: N(0, r²).", DescribeRole.Theorem),
            Node("claim-6", "map_frozen", "map frozen",
                "The frozen law. Increments.map_frozen_isometry with the isometry hypothesis weakened to constancy of the fibre law.", DescribeRole.Theorem),
            Node("claim-7", "indepFun_frozen", "indep Fun frozen",
                "The frozen independence. The padded increment is independent of the past it was read against.", DescribeRole.Theorem),
            Node("claim-8", "map_pi_of_stepIndep", "map pi of step Indep",
                "hincl at every horizon. The induction is on the horizon: the pair (X k, (X i)_{i<k}) has law ν ⊗ πν by independence, and Fin.insertNthEquiv at Fin.last k turns ν ⊗ πν into π ν on Fin (k+1).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
