using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0070Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0070.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0070",
        H("Original frontier context coverage 0070"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03364", "selected_cut_03364", "Selected cut at depth 13, code 27706, node 106103",
                "At remaining fuel 8 and original index 106103, selection on the full partial prefix of depth 13 and code 27706 returns the complete row with depth 13, base-four code 27706, original node 106103, kind 2, reserved field 0, 3117 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03410", "selected_cut_03410", "Selected cut at depth 13, code 27752, node 107489",
                "At remaining fuel 8 and original index 107489, selection on the full partial prefix of depth 13 and code 27752 returns the complete row with depth 13, base-four code 27752, original node 107489, kind 2, reserved field 0, 1461 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-27705-106039", "unmarked_context_13_27705_106039", "Unmarked parent at depth 13, code 27705",
                "The frontier Boolean is false at remaining fuel 8, original node 106039, the whole prefixCache at depth 13 and code 27705, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6937-107450", "unmarked_context_12_6937_107450", "Unmarked parent at depth 12, code 6937",
                "The frontier Boolean is false at remaining fuel 9, original node 107450, the whole prefixCache at depth 12 and code 6937, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-27705-106039", "node_context_13_27705_106039", "Original split at fuel 8 and node 106039",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 105978, 105998, 106022, 106038. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6937-107450", "node_context_12_6937_107450", "Original split at fuel 9 and node 107450",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 107351, 107402, 107435, 107449. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-27705-106039", "context_13_27705_106039", "Context at depth 13, code 27705, node 106039",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27705 and original node 106039, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_110820_105978, context_14_110821_105998, context_14_110822_106022, context_14_110823_106038.", DescribeRole.Theorem),
            Node("context-13-27752-107489", "context_13_27752_107489", "Context at depth 13, code 27752, node 107489",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27752 and original node 107489, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
