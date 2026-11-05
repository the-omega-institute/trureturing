using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MertensGridGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary grid and cylinder domination growth", H("Ordinary grid and cylinder domination growth"), Blocks(
            Node("counts", "Actual labelled subsets", "count", "The count is the cardinality of the existing ordinary dominating-set family. Every distinct subset is counted once, including nonminimal subsets; no symmetry quotient is taken. The grid and cylinder use Mathlib pathGraph, cycleGraph and the Cartesian graph product.", DescribeRole.Definition),
            Node("target", "Complete joint target", "JointGrowth", "The target is an existential real mu in [1,2]. For every positive epsilon a single natural N at least three must work for both counts and every pair m,n at least N. There is no restriction on either aspect ratio. This definition records the entire Mertens source conjecture; the finite comparison alone does not prove it.", DescribeRole.Definition),
            Node("seam", "Finite seam repair", "finite_seam_bound", "For m at least three and every natural n, g(m,n) is at most c(m,n), which is at most g(m,n) times 4 to the power n. The lower inequality uses pathGraph_le_cycleGraph. The upper inequality fills both endpoint columns. The pair consisting of the repaired grid-dominating subset and the original boundary intersection determines the original cylinder subset, giving an injection into the product of the grid family and the boundary powerset. This is valid for all labelled ordinary subsets. The source event has n at least one; the finite lemma also includes the empty height.", DescribeRole.Theorem),
            Paragraph(Text("Source: Stephan Mertens, Journal of Integer Sequences 27 (2024), Article 24.7.6, definitions on pp. 1–2, joint growth discussion (15)–(17), and the conjecture immediately after (22) on p. 19. The journal and arXiv v1 have different pagination. The finite bound requires no grid-limit assumption. The remaining obligations for the complete target are an actual block-choice tiling injection, existence of the unrestricted grid joint limit, and the uniform real-power squeeze. No theorem in this document asserts that these obligations are discharged."))), []));

    private static DocumentBlock Node(string id, string title, string name, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
