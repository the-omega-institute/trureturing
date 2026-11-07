using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full original adaptive root and original score lower bound",
        H("The full original adaptive root and original score lower bound"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("The score statement ranges over all events on the original twenty four-valued coordinates with the original coefficient functions F1 and F2. The proof combines exact root coverage with every cut response and the rank-descent lower-bound theorem.")),
            Node("accepted-original-root", "accepted_original_root", "The adaptive checker at the full original root",
                "The statement is checker equality to true at fuel twenty-one, EJMOriginalGlobalDAGData.root, the original initial cache and empty partial assignment. Its proof specializes context_0_0_1558776 by unfolding the canonical prefix objects and original root.", DescribeRole.Theorem),
            Node("original-score-lower-bound", "original_score_lower_bound", "The original F1/F2 score is bounded below by scale for every event",
                "The statement quantifies over every original event and concludes scale at most score F1 F2. The proof applies checked_global_lower_bound with the original validity and symmetry facts, frontier_responses all_cut_responses, and accepted_original_root. No smaller event space or altered certificate appears in this application.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
