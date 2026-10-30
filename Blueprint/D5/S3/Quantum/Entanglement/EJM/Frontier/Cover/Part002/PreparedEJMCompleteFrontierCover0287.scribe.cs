using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0287Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0287.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0287",
        H("Original frontier context coverage 0287"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13779", "selected_cut_13779", "Selected cut at depth 13, code 107652, node 360580",
                "At remaining fuel 8 and original index 360580, selection on the full partial prefix of depth 13 and code 107652 returns the complete row with depth 13, base-four code 107652, original node 360580, kind 2, reserved field 0, 1097 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13826", "selected_cut_13826", "Selected cut at depth 13, code 107699, node 361539",
                "At remaining fuel 8 and original index 361539, selection on the full partial prefix of depth 13 and code 107699 returns the complete row with depth 13, base-four code 107699, original node 361539, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26912-360568", "unmarked_context_12_26912_360568", "Unmarked parent at depth 12, code 26912",
                "The frontier Boolean is false at remaining fuel 9, original node 360568, the whole prefixCache at depth 12 and code 26912, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26924-361540", "unmarked_context_12_26924_361540", "Unmarked parent at depth 12, code 26924",
                "The frontier Boolean is false at remaining fuel 9, original node 361540, the whole prefixCache at depth 12 and code 26924, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26912-360568", "node_context_12_26912_360568", "Original split at fuel 9 and node 360568",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 360522, 360543, 360561, 360567. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26924-361540", "node_context_12_26924_361540", "Original split at fuel 9 and node 361540",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 361484, 361516, 361533, 361539. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26912-360568", "context_12_26912_360568", "Context at depth 12, code 26912, node 360568",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26912 and original node 360568, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_107648_360522, context_13_107649_360543, context_13_107650_360561, context_13_107651_360567.", DescribeRole.Theorem),
            Node("context-12-26924-361540", "context_12_26924_361540", "Context at depth 12, code 26924, node 361540",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26924 and original node 361540, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_107696_361484, context_13_107697_361516, context_13_107698_361533, context_13_107699_361539.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
