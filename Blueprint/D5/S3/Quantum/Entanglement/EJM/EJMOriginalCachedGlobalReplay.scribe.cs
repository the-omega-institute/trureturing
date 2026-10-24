using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalCachedGlobalReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalCachedGlobalReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound replay on the full original EJM domain",
        H("Sound replay on the full original EJM domain"),
        Blocks(
            Paragraph(Text("The original F1/F2 score, scale 6,987,435, twenty four-outcome coordinates and thirty-two actual local blocks are unchanged. Full replay acceptance is an explicit, still separate obligation; conditional soundness is not an unconditional nonlocality result.")),
            Node("Prefix", "Prefix", "Every future original coordinate remains unknown",
                "The remaining fuel determines the actual original prefix depth, and every coordinate at or beyond it is unknown.", DescribeRole.Definition),
            Node("Valid", "Valid", "Keep the whole original cache association",
                "The fuel-prefix invariant and every original block association are retained together.", DescribeRole.Definition),
            Node("initial-valid", "initial_valid", "The actual empty starting context is valid",
                "The actual original initial cache represents the empty global partial assignment and satisfies the whole fuel-prefix invariant.", DescribeRole.Theorem),
            Node("step-valid", "step_valid", "Every actual original split preserves validity",
                "The literal fuel-checked split coordinate is still unknown. The complete original local transition receipts preserve all thirty-two block associations.", DescribeRole.Theorem),
            Node("valid-lower-le-score", "valid_lower_le_score", "The actual cache lower bounds every compatible completion",
                "The original full cache-soundness theorem applies to every compatible complete twenty-coordinate event with the unchanged exact score.", DescribeRole.Theorem),
            Node("globalAccepted", "globalAccepted", "The complete original acceptance obligation",
                "This proposition is the full actual root check with fuel twenty-one, actual original initial cache and empty partial assignment. It is not an imported producer verdict.", DescribeRole.Definition),
            Node("accepted-score-lower-bound", "accepted_score_lower_bound", "Full original acceptance implies the exact score bound",
                "The verified generic replay consumes every concrete original invariant, score symmetry and rank-descent law. Complete actual acceptance is required.", DescribeRole.Theorem),
            Node("accepted-prefix-score-lower-bound", "accepted_prefix_score_lower_bound", "Exact checked frontier suffixes imply the same original bound",
                "The prefix and every full-context suffix receipt must both be accepted. Their composition supplies the same complete actual replay.", DescribeRole.Theorem),
            Node("accepted-score-positive", "accepted_score_positive", "Full actual acceptance implies strict positive score",
                "The original exact scale is positive, so the conditional exact lower bound implies score at least one.", DescribeRole.Theorem),
            Node("accepted-excludes-triangle-local", "accepted_excludes_triangle_local", "Full actual acceptance excludes the original triangle-local law",
                "The existing continuous independent-source inflation theorem turns the positive original score into exclusion of triangle locality. The full original acceptance premise remains required.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
