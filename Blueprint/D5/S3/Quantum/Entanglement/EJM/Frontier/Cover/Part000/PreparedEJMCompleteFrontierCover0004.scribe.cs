using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0004Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0004.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0004",
        H("Original frontier context coverage 0004"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00194", "selected_cut_00194", "Selected cut at depth 13, code 1202, node 11323",
                "At remaining fuel 8 and original index 11323, selection on the full partial prefix of depth 13 and code 1202 returns the complete row with depth 13, base-four code 1202, original node 11323, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00241", "selected_cut_00241", "Selected cut at depth 12, code 361, node 13202",
                "At remaining fuel 9 and original index 13202, selection on the full partial prefix of depth 12 and code 361 returns the complete row with depth 12, base-four code 361, original node 13202, kind 2, reserved field 0, 2661 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-300-11355", "unmarked_context_12_300_11355", "Unmarked parent at depth 12, code 300",
                "The frontier Boolean is false at remaining fuel 9, original node 11355, the whole prefixCache at depth 12 and code 300, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-89-13078", "unmarked_context_11_89_13078", "Unmarked parent at depth 11, code 89",
                "The frontier Boolean is false at remaining fuel 10, original node 13078, the whole prefixCache at depth 11 and code 89, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-300-11355", "node_context_12_300_11355", "Original split at fuel 9 and node 11355",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 11156, 11251, 11323, 11354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-89-13078", "node_context_11_89_13078", "Original split at fuel 10 and node 13078",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 12688, 12871, 12985, 13077. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1202-11323", "context_13_1202_11323", "Context at depth 13, code 1202, node 11323",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1202 and original node 11323, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-361-13202", "context_12_361_13202", "Context at depth 12, code 361, node 13202",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 361 and original node 13202, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
