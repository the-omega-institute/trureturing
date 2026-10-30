using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1086Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1086.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1086",
        H("Original frontier context coverage 1086"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52131", "selected_cut_52131", "Selected cut at depth 11, code 287436, node 1514012",
                "At remaining fuel 10 and original index 1514012, selection on the full partial prefix of depth 11 and code 287436 returns the complete row with depth 11, base-four code 287436, original node 1514012, kind 2, reserved field 0, 2689 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52178", "selected_cut_52178", "Selected cut at depth 11, code 287624, node 1516867",
                "At remaining fuel 10 and original index 1516867, selection on the full partial prefix of depth 11 and code 287624 returns the complete row with depth 11, base-four code 287624, original node 1516867, kind 2, reserved field 0, 2777 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-71859-1514075", "unmarked_context_10_71859_1514075", "Unmarked parent at depth 10, code 71859",
                "The frontier Boolean is false at remaining fuel 11, original node 1514075, the whole prefixCache at depth 10 and code 71859, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-71905-1516796", "unmarked_context_10_71905_1516796", "Unmarked parent at depth 10, code 71905",
                "The frontier Boolean is false at remaining fuel 11, original node 1516796, the whole prefixCache at depth 10 and code 71905, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-71859-1514075", "node_context_10_71859_1514075", "Original split at fuel 11 and node 1514075",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1514012, 1514049, 1514074, 1470044. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-71905-1516796", "node_context_10_71905_1516796", "Original split at fuel 11 and node 1516796",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1516580, 1468419, 1516692, 1516795. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-287436-1514012", "context_11_287436_1514012", "Context at depth 11, code 287436, node 1514012",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 287436 and original node 1514012, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-287624-1516867", "context_11_287624_1516867", "Context at depth 11, code 287624, node 1516867",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 287624 and original node 1516867, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
