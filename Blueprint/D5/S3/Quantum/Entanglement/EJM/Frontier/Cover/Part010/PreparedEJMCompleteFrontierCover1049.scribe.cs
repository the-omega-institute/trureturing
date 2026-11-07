using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1049Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1049.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1049",
        H("Original frontier context coverage 1049"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50356", "selected_cut_50356", "Selected cut at depth 11, code 106144, node 1375697",
                "At remaining fuel 10 and original index 1375697, selection on the full partial prefix of depth 11 and code 106144 returns the complete row with depth 11, base-four code 106144, original node 1375697, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50403", "selected_cut_50403", "Selected cut at depth 11, code 106194, node 1439290",
                "At remaining fuel 10 and original index 1439290, selection on the full partial prefix of depth 11 and code 106194 returns the complete row with depth 11, base-four code 106194, original node 1439290, kind 2, reserved field 0, 2425 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6633-1437541", "unmarked_context_9_6633_1437541", "Unmarked parent at depth 9, code 6633",
                "The frontier Boolean is false at remaining fuel 12, original node 1437541, the whole prefixCache at depth 9 and code 6633, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6636-1439112", "unmarked_context_9_6636_1439112", "Unmarked parent at depth 9, code 6636",
                "The frontier Boolean is false at remaining fuel 12, original node 1439112, the whole prefixCache at depth 9 and code 6636, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6633-1437541", "node_context_9_6633_1437541", "Original split at fuel 12 and node 1437541",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1437193, 893098, 1437362, 1437540. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6636-1439112", "node_context_9_6636_1439112", "Original split at fuel 12 and node 1439112",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1438143, 1438510, 1438821, 1439111. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-6633-1437541", "context_9_6633_1437541", "Context at depth 9, code 6633, node 1437541",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6633 and original node 1437541, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_26532_1437193, context_10_26533_893098, context_10_26534_1437362, context_10_26535_1437540.", DescribeRole.Theorem),
            Node("context-11-106194-1439290", "context_11_106194_1439290", "Context at depth 11, code 106194, node 1439290",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106194 and original node 1439290, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
