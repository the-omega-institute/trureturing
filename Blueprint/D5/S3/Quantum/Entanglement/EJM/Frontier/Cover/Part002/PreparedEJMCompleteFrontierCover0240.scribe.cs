using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0240Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0240.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0240",
        H("Original frontier context coverage 0240"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11522", "selected_cut_11522", "Selected cut at depth 13, code 102692, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 102692 returns the complete row with depth 13, base-four code 102692, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11570", "selected_cut_11570", "Selected cut at depth 13, code 102761, node 309164",
                "At remaining fuel 8 and original index 309164, selection on the full partial prefix of depth 13 and code 102761 returns the complete row with depth 13, base-four code 102761, original node 309164, kind 2, reserved field 0, 1333 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25673-308057", "unmarked_context_12_25673_308057", "Unmarked parent at depth 12, code 25673",
                "The frontier Boolean is false at remaining fuel 9, original node 308057, the whole prefixCache at depth 12 and code 25673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25688-309078", "unmarked_context_12_25688_309078", "Unmarked parent at depth 12, code 25688",
                "The frontier Boolean is false at remaining fuel 9, original node 309078, the whole prefixCache at depth 12 and code 25688, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25673-308057", "node_context_12_25673_308057", "Original split at fuel 9 and node 308057",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 307997, 308037, 308056. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25688-309078", "node_context_12_25688_309078", "Original split at fuel 9 and node 309078",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 309044, 309069, 309077. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102692-3444", "context_13_102692_3444", "Context at depth 13, code 102692, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102692 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-102761-309164", "context_13_102761_309164", "Context at depth 13, code 102761, node 309164",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102761 and original node 309164, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
