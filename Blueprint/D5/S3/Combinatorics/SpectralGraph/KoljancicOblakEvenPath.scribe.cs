using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class KoljancicOblakEvenPathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/koljancic2026nssp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted branch continuants and their first variations for the even double-path nSSP question.",
        H("Even double paths with a nonempty loop set"), Blocks(
            Paragraph(Text("Koljančić and Oblak ask in Question 5.11 of arXiv:2604.21552v1 whether every even double path with at least one loop allows the non-symmetric Strong Spectral Property. Allows means existence of a real matrix with exactly the prescribed nonzero entries. The test matrix in the nSSP definition is an unrestricted real matrix, and the commutator uses its transpose.")),
            Paragraph(Text("The formal claim retains every positive even order and every nonempty loop set. It imposes no symmetry, sign, trace or spectral condition on the existential witness. The source convention on vertices numbered from one corresponds to Fin n by subtracting one.")),
            Node("pattern", "Exact double-path pattern", "pathPattern", DescribeRole.Definition,
                "Both orientations of each consecutive edge occur; the only additional arcs are the specified loops.", true),
            Node("nssp", "Non-symmetric Strong Spectral Property", "HasNSSP", DescribeRole.Definition,
                "Entrywise annihilation and the transpose commutator must force every real test matrix to vanish.", true),
            Node("claim", "Complete Question 5.11 event", "claim", DescribeRole.Definition,
                "This proposition is the full source question. No theorem in this module currently proves it.", true),
            Node("continuant", "Zero-diagonal branch continuant", "continuant", DescribeRole.Definition,
                "The empty branch has polynomial one and a one-vertex branch has polynomial X. Each successor step uses the squared weight of the newly attached edge."),
            Node("variation", "Edge-parameter first variation", "variation", DescribeRole.Definition,
                "The formal linearized recurrence includes the variation of the edge parameter and the variation of the preceding continuant. A connection to the actual characteristic-coefficient differential remains to be proved."),
            Node("recovery", "Reverse recovery of every edge variation", "branch_variation_injective", DescribeRole.Theorem,
                "At a nonzero edge-parameter sequence, two consecutive zero polynomial variations force every earlier edge variation to vanish. The leading coefficient of each continuant is one, while its variation has strictly smaller degree. Taking that coefficient in the linearized recurrence first recovers the last edge variation; cancellation and induction recover the remaining edges. Length-zero and length-one branches are included without extra parameters."),
            Node("matrix", "Actual zero-diagonal weighted branch", "weightedPath", DescribeRole.Definition,
                "The two orientations of each edge carry the same real weight. Vertex reversal aligns the first-row determinant expansion with the last edge in the recurrence. The constructor permits zero weights as well."),
            Node("characteristic", "Weighted branch characteristic correspondence", "weighted_path_charpoly", DescribeRole.Theorem,
                "The actual characteristic polynomial of the weighted branch equals the continuant with squared edge parameters, in every order including zero and one. First-row expansion uses the existing det_sparse_front supplier in ForbiddenNeighbourDeterminant; both remaining principal submatrices have the same reversed-edge convention."),
            Paragraph(Text("The remaining whole-event bridges are the weighted-matrix characteristic correspondence; a coprime choice for opposite-parity branches; separation of the complete central-vertex variation, retaining all product-rule cross terms; the coefficient/adjugate trace pairing and unrestricted real commutant argument; and exact support enlargement to every nonempty loop set. The source Superpattern Lemma also preserves similarity, which is stronger than the existential event requires.")),
            Paragraph(Text("Source attribution and license boundaries are recorded in Library/Eigenstructure/koljancic2026nssp.md. The continuant variation argument is a repository derivation; the source question and its published definitions are not claimed as new results.")))));

    private static DocumentBlock Node(string id, string title, string name, DescribeRole role, string prose,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create("koljancic-even-path-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromLean(), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
