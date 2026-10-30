using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0867Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0867.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0867",
        H("Original frontier context coverage 0867"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41619", "selected_cut_41619", "Selected cut at depth 11, code 84078, node 1137917",
                "At remaining fuel 10 and original index 1137917, selection on the full partial prefix of depth 11 and code 84078 returns the complete row with depth 11, base-four code 84078, original node 1137917, kind 2, reserved field 0, 1757 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41666", "selected_cut_41666", "Selected cut at depth 12, code 336428, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 336428 returns the complete row with depth 12, base-four code 336428, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21019-1137942", "unmarked_context_10_21019_1137942", "Unmarked parent at depth 10, code 21019",
                "The frontier Boolean is false at remaining fuel 11, original node 1137942, the whole prefixCache at depth 10 and code 21019, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84106-1139187", "unmarked_context_11_84106_1139187", "Unmarked parent at depth 11, code 84106",
                "The frontier Boolean is false at remaining fuel 10, original node 1139187, the whole prefixCache at depth 11 and code 84106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21019-1137942", "node_context_10_21019_1137942", "Original split at fuel 11 and node 1137942",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1137869, 1137893, 1137917, 1137941. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84106-1139187", "node_context_11_84106_1139187", "Original split at fuel 10 and node 1139187",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1139145, 474208, 1139186. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84078-1137917", "context_11_84078_1137917", "Context at depth 11, code 84078, node 1137917",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84078 and original node 1137917, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336428-1108174", "context_12_336428_1108174", "Context at depth 12, code 336428, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336428 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
