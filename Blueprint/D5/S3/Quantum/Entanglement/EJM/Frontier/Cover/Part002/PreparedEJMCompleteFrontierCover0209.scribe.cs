using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0209Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0209.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0209",
        H("Original frontier context coverage 0209"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10035", "selected_cut_10035", "Selected cut at depth 13, code 99438, node 275462",
                "At remaining fuel 8 and original index 275462, selection on the full partial prefix of depth 13 and code 99438 returns the complete row with depth 13, base-four code 99438, original node 275462, kind 2, reserved field 0, 1473 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10082", "selected_cut_10082", "Selected cut at depth 13, code 99485, node 276322",
                "At remaining fuel 8 and original index 276322, selection on the full partial prefix of depth 13 and code 99485 returns the complete row with depth 13, base-four code 99485, original node 276322, kind 2, reserved field 0, 2333 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24859-275469", "unmarked_context_12_24859_275469", "Unmarked parent at depth 12, code 24859",
                "The frontier Boolean is false at remaining fuel 9, original node 275469, the whole prefixCache at depth 12 and code 24859, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24870-276279", "unmarked_context_12_24870_276279", "Unmarked parent at depth 12, code 24870",
                "The frontier Boolean is false at remaining fuel 9, original node 276279, the whole prefixCache at depth 12 and code 24870, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24859-275469", "node_context_12_24859_275469", "Original split at fuel 9 and node 275469",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 275414, 275444, 275462, 275468. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24870-276279", "node_context_12_24870_276279", "Original split at fuel 9 and node 276279",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 276226, 276247, 276271, 276278. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99438-275462", "context_13_99438_275462", "Context at depth 13, code 99438, node 275462",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99438 and original node 275462, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99485-276322", "context_13_99485_276322", "Context at depth 13, code 99485, node 276322",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99485 and original node 276322, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
