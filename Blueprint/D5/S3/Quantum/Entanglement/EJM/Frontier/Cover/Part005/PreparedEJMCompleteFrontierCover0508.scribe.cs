using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0508Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0508.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0508",
        H("Original frontier context coverage 0508"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24388", "selected_cut_24388", "Selected cut at depth 12, code 77116, node 445562",
                "At remaining fuel 9 and original index 445562, selection on the full partial prefix of depth 12 and code 77116 returns the complete row with depth 12, base-four code 77116, original node 445562, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24434", "selected_cut_24434", "Selected cut at depth 13, code 308543, node 617488",
                "At remaining fuel 8 and original index 617488, selection on the full partial prefix of depth 13 and code 308543 returns the complete row with depth 13, base-four code 308543, original node 617488, kind 2, reserved field 0, 937 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19278-616491", "unmarked_context_11_19278_616491", "Unmarked parent at depth 11, code 19278",
                "The frontier Boolean is false at remaining fuel 10, original node 616491, the whole prefixCache at depth 11 and code 19278, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19283-617490", "unmarked_context_11_19283_617490", "Unmarked parent at depth 11, code 19283",
                "The frontier Boolean is false at remaining fuel 10, original node 617490, the whole prefixCache at depth 11 and code 19283, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19278-616491", "node_context_11_19278_616491", "Original split at fuel 10 and node 616491",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 616250, 616320, 616394, 616490. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19283-617490", "node_context_11_19283_617490", "Original split at fuel 10 and node 617490",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 617344, 617389, 617441, 617489. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19278-616491", "context_11_19278_616491", "Context at depth 11, code 19278, node 616491",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19278 and original node 616491, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77112_616250, context_12_77113_616320, context_12_77114_616394, context_12_77115_616490.", DescribeRole.Theorem),
            Node("context-11-19283-617490", "context_11_19283_617490", "Context at depth 11, code 19283, node 617490",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19283 and original node 617490, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77132_617344, context_12_77133_617389, context_12_77134_617441, context_12_77135_617489.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
