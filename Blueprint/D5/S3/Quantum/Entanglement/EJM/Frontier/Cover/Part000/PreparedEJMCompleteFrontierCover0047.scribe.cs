using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0047Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0047.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0047",
        H("Original frontier context coverage 0047"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02258", "selected_cut_02258", "Selected cut at depth 13, code 22595, node 74050",
                "At remaining fuel 8 and original index 74050, selection on the full partial prefix of depth 13 and code 22595 returns the complete row with depth 13, base-four code 22595, original node 74050, kind 2, reserved field 0, 1185 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02306", "selected_cut_02306", "Selected cut at depth 13, code 22631, node 75431",
                "At remaining fuel 8 and original index 75431, selection on the full partial prefix of depth 13 and code 22631 returns the complete row with depth 13, base-four code 22631, original node 75431, kind 2, reserved field 0, 1165 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5648-74051", "unmarked_context_12_5648_74051", "Unmarked parent at depth 12, code 5648",
                "The frontier Boolean is false at remaining fuel 9, original node 74051, the whole prefixCache at depth 12 and code 5648, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5656-75318", "unmarked_context_12_5656_75318", "Unmarked parent at depth 12, code 5656",
                "The frontier Boolean is false at remaining fuel 9, original node 75318, the whole prefixCache at depth 12 and code 5656, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5648-74051", "node_context_12_5648_74051", "Original split at fuel 9 and node 74051",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 73986, 74013, 74040, 74050. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5656-75318", "node_context_12_5656_75318", "Original split at fuel 9 and node 75318",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 75224, 75261, 75290, 75317. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-22595-74050", "context_13_22595_74050", "Context at depth 13, code 22595, node 74050",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22595 and original node 74050, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22631-75431", "context_13_22631_75431", "Context at depth 13, code 22631, node 75431",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22631 and original node 75431, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
