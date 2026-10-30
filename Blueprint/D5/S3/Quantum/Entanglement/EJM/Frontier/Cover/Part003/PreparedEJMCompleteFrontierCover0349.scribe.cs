using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0349Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0349.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0349",
        H("Original frontier context coverage 0349"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16755", "selected_cut_16755", "Selected cut at depth 13, code 113796, node 426807",
                "At remaining fuel 8 and original index 426807, selection on the full partial prefix of depth 13 and code 113796 returns the complete row with depth 13, base-four code 113796, original node 426807, kind 2, reserved field 0, 1593 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16803", "selected_cut_16803", "Selected cut at depth 13, code 113844, node 427787",
                "At remaining fuel 8 and original index 427787, selection on the full partial prefix of depth 13 and code 113844 returns the complete row with depth 13, base-four code 113844, original node 427787, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28449-426881", "unmarked_context_12_28449_426881", "Unmarked parent at depth 12, code 28449",
                "The frontier Boolean is false at remaining fuel 9, original node 426881, the whole prefixCache at depth 12 and code 28449, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28460-427768", "unmarked_context_12_28460_427768", "Unmarked parent at depth 12, code 28460",
                "The frontier Boolean is false at remaining fuel 9, original node 427768, the whole prefixCache at depth 12 and code 28460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28449-426881", "node_context_12_28449_426881", "Original split at fuel 9 and node 426881",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 426807, 426850, 426874, 426880. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28460-427768", "node_context_12_28460_427768", "Original split at fuel 9 and node 427768",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 427717, 427747, 427762, 427767. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113796-426807", "context_13_113796_426807", "Context at depth 13, code 113796, node 426807",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113796 and original node 426807, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-113844-427787", "context_13_113844_427787", "Context at depth 13, code 113844, node 427787",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113844 and original node 427787, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
