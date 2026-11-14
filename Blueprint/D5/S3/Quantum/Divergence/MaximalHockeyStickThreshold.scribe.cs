using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickThreshold.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted threshold optimality in the faithful interior",
        H("Weighted threshold optimality in the faithful interior"), Blocks(
            Paragraph(Text("These finite matrix statements separate the positive-definite interior argument from later singular support reduction. The scalar canonical overlap is an antecedent of the Hiai canonical spectral preparation; its optimality for arbitrary weights is not assumed.")),
            Node("weighted_overlap_optimal_iff", "For Hermitian A,B, positive-definite W,Y and Y<=A,B, Y maximizes Re Tr(WX) over PSD common lower bounds exactly when (A-Y) W (B-Y)=0. Congruence by sqrt(W), interior relaxation and Hermitian trace uniqueness prove the equivalence. The diagonal common-corner criterion consumes it.", true, false),
            Node("canonicalOverlap", "canonicalOverlap D t is the functional calculus of x -> min(x,t(1-x)). It is defined for arbitrary real t. Its PSD feasibility requires the contraction and nonnegative-threshold hypotheses proved elsewhere.", false, false),
            Node("canonical_residuals", "For Hermitian D and every real t, D-canonicalOverlap(D,t)=thresholdPositive(D,t), and t(1-D)-canonicalOverlap(D,t)=thresholdNegative(D,t). The one-threshold criterion uses both exact residual identities.", true, false),
            Node("canonical_optimal_iff", "For Hermitian D with all eigenvalues in (0,1), positive-definite W and t>0, the canonical overlap maximizes the weighted PSD trace exactly when thresholdPositive(D,t) W thresholdNegative(D,t)=0. The candidate is positive definite in this scope. SingularCriterion obtains its broader scope by compression.", true, false),
            Node("canonical_all_thresholds_iff_commute", "For a strict positive contraction D and positive-definite W, canonical weighted optimality at every positive threshold is equivalent to WD=DW. This combines the one-threshold condition with spectral separation and serves the common-interior analysis.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-threshold-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
