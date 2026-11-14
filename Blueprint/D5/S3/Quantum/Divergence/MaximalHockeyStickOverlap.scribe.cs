using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual PSD overlap optimization and Hermitian trace uniqueness",
        H("The actual PSD overlap optimization and Hermitian trace uniqueness"), Blocks(
            Paragraph(Text("The common-PSD overlap is a finite matrix optimization, including zero matrices and the empty index type. Its operational interpretation is established by MaximalHockeyStickOperational, following HMT Proposition V.1. The Hermitian relaxation used internally is a different feasible set and is not silently assumed positive.")),
            Node("positiveOverlaps", "positiveOverlaps A B consists exactly of matrices X with 0 <= X, X <= A and X <= B in Loewner order. Both upper bounds are retained. Profile, support localization and actual reverse preparations consume this feasible set.", false, false),
            Node("overlapValue", "overlapValue A B is the real supremum of Re Tr(X) over positiveOverlaps A B. Compactness and a zero feasible point supply attainment for PSD A,B; no normalization is imposed. maximalHockey and the operational representation consume this objective.", false, false),
            Node("maximalHockey", "maximalHockey A B t is Re Tr(A) minus overlapValue A (t B). This definition is an SDP expression. Operational.operational_hockey_eq proves its equality to the infimum of the actual sums max(p_i-t q_i,0) for t>0; the general convex kernel consumes that bridge.", false, false),
            Node("overlap_attained", "For every PSD A,B there exists an actual positive common lower bound whose real trace equals overlapValue A B. The closed feasible set is bounded by A, hence compact in finite dimension. Profile regularity and the three-component operational construction use the maximizing matrix, including singular and zero cases.", true, false),
            Node("positive_residual_unique", "For Hermitian H and PSD T with T-H also PSD, Re Tr(H_+) <= Re Tr(T); equality forces T=H_+. The proof diagonalizes H, bounds each diagonal residual, and eliminates zero diagonal columns by positivity. The Hermitian common-lower-bound uniqueness theorem consumes this rigidity.", true, false),
            Node("hermitian_overlap_unique", "For Hermitian U,V, X0=U-(U-V)_+ is Hermitian and below both. Every Hermitian X below both has trace at most Tr(X0), with equality only for X=X0. No claim that X0 is PSD is made. Threshold uses this uniqueness after the interior positivity constraint has been removed.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-overlap-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
