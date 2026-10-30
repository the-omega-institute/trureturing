using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1034Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1034.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1034",
        H("Original frontier context coverage 1034"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49636", "selected_cut_49636", "Selected cut at depth 11, code 102094, node 1405656",
                "At remaining fuel 10 and original index 1405656, selection on the full partial prefix of depth 11 and code 102094 returns the complete row with depth 11, base-four code 102094, original node 1405656, kind 2, reserved field 0, 2721 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49682", "selected_cut_49682", "Selected cut at depth 12, code 408611, node 1407489",
                "At remaining fuel 9 and original index 1407489, selection on the full partial prefix of depth 12 and code 408611 returns the complete row with depth 12, base-four code 408611, original node 1407489, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25523-1405715", "unmarked_context_10_25523_1405715", "Unmarked parent at depth 10, code 25523",
                "The frontier Boolean is false at remaining fuel 11, original node 1405715, the whole prefixCache at depth 10 and code 25523, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-102152-1407490", "unmarked_context_11_102152_1407490", "Unmarked parent at depth 11, code 102152",
                "The frontier Boolean is false at remaining fuel 10, original node 1407490, the whole prefixCache at depth 11 and code 102152, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25523-1405715", "node_context_10_25523_1405715", "Original split at fuel 11 and node 1405715",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1405541, 1405604, 1405656, 1405714. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-102152-1407490", "node_context_11_102152_1407490", "Original split at fuel 10 and node 1407490",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1407389, 1407440, 1407489. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-102094-1405656", "context_11_102094_1405656", "Context at depth 11, code 102094, node 1405656",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102094 and original node 1405656, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-102152-1407490", "context_11_102152_1407490", "Context at depth 11, code 102152, node 1407490",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102152 and original node 1407490, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_408608_1108174, context_12_408609_1407389, context_12_408610_1407440, context_12_408611_1407489.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
