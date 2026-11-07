using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0809Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0809.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0809",
        H("Original frontier context coverage 0809"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38835", "selected_cut_38835", "Selected cut at depth 12, code 302115, node 1050455",
                "At remaining fuel 9 and original index 1050455, selection on the full partial prefix of depth 12 and code 302115 returns the complete row with depth 12, base-four code 302115, original node 1050455, kind 2, reserved field 0, 3145 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38882", "selected_cut_38882", "Selected cut at depth 12, code 302180, node 1052439",
                "At remaining fuel 9 and original index 1052439, selection on the full partial prefix of depth 12 and code 302180 returns the complete row with depth 12, base-four code 302180, original node 1052439, kind 2, reserved field 0, 1865 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75528-1050456", "unmarked_context_11_75528_1050456", "Unmarked parent at depth 11, code 75528",
                "The frontier Boolean is false at remaining fuel 10, original node 1050456, the whole prefixCache at depth 11 and code 75528, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75544-1052413", "unmarked_context_11_75544_1052413", "Unmarked parent at depth 11, code 75544",
                "The frontier Boolean is false at remaining fuel 10, original node 1052413, the whole prefixCache at depth 11 and code 75544, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75528-1050456", "node_context_11_75528_1050456", "Original split at fuel 10 and node 1050456",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1050349, 1050403, 1050455. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75544-1052413", "node_context_11_75544_1052413", "Original split at fuel 10 and node 1052413",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1052360, 1052387, 1052412. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302115-1050455", "context_12_302115_1050455", "Context at depth 12, code 302115, node 1050455",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302115 and original node 1050455, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302180-1052439", "context_12_302180_1052439", "Context at depth 12, code 302180, node 1052439",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302180 and original node 1052439, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
