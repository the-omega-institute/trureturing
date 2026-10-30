using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0163Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0163.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0163",
        H("Original frontier context coverage 0163"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07827", "selected_cut_07827", "Selected cut at depth 12, code 22686, node 224159",
                "At remaining fuel 9 and original index 224159, selection on the full partial prefix of depth 12 and code 22686 returns the complete row with depth 12, base-four code 22686, original node 224159, kind 2, reserved field 0, 2101 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07873", "selected_cut_07873", "Selected cut at depth 13, code 91141, node 225147",
                "At remaining fuel 8 and original index 225147, selection on the full partial prefix of depth 13 and code 91141 returns the complete row with depth 13, base-four code 91141, original node 225147, kind 2, reserved field 0, 2801 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5671-224181", "unmarked_context_11_5671_224181", "Unmarked parent at depth 11, code 5671",
                "The frontier Boolean is false at remaining fuel 10, original node 224181, the whole prefixCache at depth 11 and code 5671, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-88-225090", "unmarked_context_8_88_225090", "Unmarked parent at depth 8, code 88",
                "The frontier Boolean is false at remaining fuel 13, original node 225090, the whole prefixCache at depth 8 and code 88, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5671-224181", "node_context_11_5671_224181", "Original split at fuel 10 and node 224181",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 224121, 224139, 224159, 224180. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-88-225090", "node_context_8_88_225090", "Original split at fuel 13 and node 225090",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 219365, 223301, 224697, 225089. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22686-224159", "context_12_22686_224159", "Context at depth 12, code 22686, node 224159",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22686 and original node 224159, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-91141-225147", "context_13_91141_225147", "Context at depth 13, code 91141, node 225147",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91141 and original node 225147, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
