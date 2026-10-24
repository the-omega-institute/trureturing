using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMGlobalScoreSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMGlobalScoreSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual original EJM source and outcome symmetry",
        H("Actual original EJM source and outcome symmetry"),
        Blocks(
            Paragraph(Text("The original 192 source-copy actions and 24 common outcome actions preserve the same F1/F2 score. A cut keeps its actual pivot in the natural twenty-coordinate order.")),
            Node("cutOfTag", "cutOfTag", "Decode the actual source-major symmetry tag",
                "The tag specifies the original source action and common outcome permutation, retaining the actual pivot.", DescribeRole.Definition),
            Node("act", "act", "Apply the complete original event action",
                "The whole original source-copy map and common outcome permutation act on the complete event.", DescribeRole.Definition),
            Node("actual-score-invariant", "actual_score_invariant", "The unchanged original score is invariant",
                "The existing original source-action and outcome-relabeling laws prove equality of the exact F1/F2 score.", DescribeRole.Theorem),
            Node("dominates", "dominates", "Check the original pivot and all earlier coordinates",
                "The pivot strictly decreases; each earlier coordinate is either fixed by the whole action or checked on its actual assigned values.", DescribeRole.Definition),
            Node("dominates-rank-lt", "dominates_rank_lt", "Every compatible original event has smaller rank",
                "The actual-context cut supplies the finite lexicographic domination witness. Its whole-event action strictly decreases the natural rank.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
