using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class TripartiteH1RepairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TripartiteH1Repair.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/dotterrer2012coboundary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-tripartite H1 exactness, antipodal minimum representatives, and exact "
            + "degree-one repair coefficients on the octahedron.",
        H("Tripartite degree-one cochain repair"),
        Blocks(
            Node("edge-cochain", "Three actual edge families", "Edge",
                "An edge cochain has independent AB, AC, and BC values on the corresponding "
                    + "Cartesian products.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("vertex-potential", "Vertex potentials", "Potential",
                "A potential assigns one F2 value to each vertex in each of the three parts.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("vertex-coboundary", "Vertex coboundary", "d0",
                "Each edge receives the sum of its two endpoint potentials.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("triangle-defect", "Triangle defect", "d1",
                "The defect of an actual ABC triangle is the sum of its three edge values.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("degree-one-exactness", "Complete-tripartite degree-one exactness",
                "ker_d1_eq_im_d0",
                "Each vertex cancels twice in the triangle defect of a coboundary. For "
                    + "arbitrary nonempty parts, vanishing defects are equivalent to one global "
                    + "vertex potential. The reverse proof reconstructs the potential from "
                    + "anchored AB and AC rows and uses triangle equations on all three families.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("edge-weight", "Edge support weight", "weight",
                "On three Bool parts, the weight counts all twelve actual edges, grouped by family.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("defect-count", "Triangle defect count", "defects",
                "The count ranges over the eight actual ABC triangles.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("three-edge-cochain", "Three-edge witness", "witness",
                "The support is AB(false,true), AC(false,false), and BC(false,false).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("dual-cube", "Dual cube vertices", "Cube",
                "The eight triangles are the vertices of the dual three-dimensional cube.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("antipode", "Antipodal triangles", "antipode",
                "All three Bool coordinates are complemented.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("dual-path", "Coordinate dual path", "cubePath",
                "The path changes the A, B, then C coordinate, omitting stationary steps. "
                    + "Its primal edge cochain has boundary equal to the two endpoints.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("sharpness", "Minimum representative of every antipodal defect fiber",
                "sharp_three_edge_witness",
                "For every cochain with an arbitrary antipodal defect pair, three coordinate "
                    + "cuts force every vertex repair to retain at least three edges. Exactness "
                    + "constructs a potential reaching the displayed coordinate path. The same "
                    + "public statement unconditionally gives the named witness's literal "
                    + "AB(false,true), AC(false,false), and BC(false,false) support, exactly the "
                    + "defects (false,true,true) and (true,false,false), weight three, defect "
                    + "count two, and a weight-three lower bound for every vertex repair.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("universal-repair", "Exact octahedral degree-one repair coefficient", "universal_repair",
                "For any natural p and q, a universal repair with q times edge weight at most "
                    + "p times defect count exists exactly when three times q is at most twice p. "
                    + "This includes the global twice-weight versus three-defects bound. The "
                    + "upper estimate is prior literature, Dotterrer--Kahle Proposition 5.5 "
                    + "at n=3, k=1 in support-count norms. Its structural proof here pairs the "
                    + "even defect vertices by dual cube paths of at most three edges, then uses "
                    + "exactness. The published upper estimate proves sufficiency, while the "
                    + "antipodal cut barrier proves necessity and determines the exact coefficient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);
}
