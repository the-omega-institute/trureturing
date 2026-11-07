using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0189Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0189.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0189",
        H("Original frontier context coverage 0189"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09075", "selected_cut_09075", "Selected cut at depth 14, code 372870, node 251500",
                "At remaining fuel 7 and original index 251500, selection on the full partial prefix of depth 14 and code 372870 returns the complete row with depth 14, base-four code 372870, original node 251500, kind 2, reserved field 0, 1173 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09123", "selected_cut_09123", "Selected cut at depth 14, code 372978, node 252758",
                "At remaining fuel 7 and original index 252758, selection on the full partial prefix of depth 14 and code 372978 returns the complete row with depth 14, base-four code 372978, original node 252758, kind 2, reserved field 0, 1825 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-93217-251514", "unmarked_context_13_93217_251514", "Unmarked parent at depth 13, code 93217",
                "The frontier Boolean is false at remaining fuel 8, original node 251514, the whole prefixCache at depth 13 and code 93217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23310-252688", "unmarked_context_12_23310_252688", "Unmarked parent at depth 12, code 23310",
                "The frontier Boolean is false at remaining fuel 9, original node 252688, the whole prefixCache at depth 12 and code 23310, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-93217-251514", "node_context_13_93217_251514", "Original split at fuel 8 and node 251514",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 251458, 251481, 251500, 251513. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23310-252688", "node_context_12_23310_252688", "Original split at fuel 9 and node 252688",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 252547, 252638, 252674, 252687. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-372870-251500", "context_14_372870_251500", "Context at depth 14, code 372870, node 251500",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 372870 and original node 251500, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-372978-252758", "context_14_372978_252758", "Context at depth 14, code 372978, node 252758",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 372978 and original node 252758, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
