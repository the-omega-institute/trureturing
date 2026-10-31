using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0306Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0306.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0306",
        H("Original frontier context coverage 0306"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14692", "selected_cut_14692", "Selected cut at depth 14, code 438517, node 379019",
                "At remaining fuel 7 and original index 379019, selection on the full partial prefix of depth 14 and code 438517 returns the complete row with depth 14, base-four code 438517, original node 379019, kind 2, reserved field 0, 1601 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14739", "selected_cut_14739", "Selected cut at depth 13, code 109674, node 380137",
                "At remaining fuel 8 and original index 380137, selection on the full partial prefix of depth 13 and code 109674 returns the complete row with depth 13, base-four code 109674, original node 380137, kind 2, reserved field 0, 1649 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-109629-379101", "unmarked_context_13_109629_379101", "Unmarked parent at depth 13, code 109629",
                "The frontier Boolean is false at remaining fuel 8, original node 379101, the whole prefixCache at depth 13 and code 109629, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27417-380071", "unmarked_context_12_27417_380071", "Unmarked parent at depth 12, code 27417",
                "The frontier Boolean is false at remaining fuel 9, original node 380071, the whole prefixCache at depth 12 and code 27417, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-109629-379101", "node_context_13_109629_379101", "Original split at fuel 8 and node 379101",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 378977, 379019, 379061, 379100. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27417-380071", "node_context_12_27417_380071", "Original split at fuel 9 and node 380071",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 380018, 380049, 380065, 380070. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-438517-379019", "context_14_438517_379019", "Context at depth 14, code 438517, node 379019",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 438517 and original node 379019, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109674-380137", "context_13_109674_380137", "Context at depth 13, code 109674, node 380137",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109674 and original node 380137, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
