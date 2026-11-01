using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0201Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0201.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0201",
        H("Original frontier context coverage 0201"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09650", "selected_cut_09650", "Selected cut at depth 12, code 24596, node 266363",
                "At remaining fuel 9 and original index 266363, selection on the full partial prefix of depth 12 and code 24596 returns the complete row with depth 12, base-four code 24596, original node 266363, kind 2, reserved field 0, 3561 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09698", "selected_cut_09698", "Selected cut at depth 12, code 24623, node 267817",
                "At remaining fuel 9 and original index 267817, selection on the full partial prefix of depth 12 and code 24623 returns the complete row with depth 12, base-four code 24623, original node 267817, kind 2, reserved field 0, 3729 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6148-266308", "unmarked_context_11_6148_266308", "Unmarked parent at depth 11, code 6148",
                "The frontier Boolean is false at remaining fuel 10, original node 266308, the whole prefixCache at depth 11 and code 6148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6154-267623", "unmarked_context_11_6154_267623", "Unmarked parent at depth 11, code 6154",
                "The frontier Boolean is false at remaining fuel 10, original node 267623, the whole prefixCache at depth 11 and code 6154, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6148-266308", "node_context_11_6148_266308", "Original split at fuel 10 and node 266308",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 266170, 266216, 266261, 266307. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6154-267623", "node_context_11_6154_267623", "Original split at fuel 10 and node 267623",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 267475, 267525, 267574, 267622. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6148-266308", "context_11_6148_266308", "Context at depth 11, code 6148, node 266308",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6148 and original node 266308, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_24592_266170, context_12_24593_266216, context_12_24594_266261, context_12_24595_266307.", DescribeRole.Theorem),
            Node("context-12-24623-267817", "context_12_24623_267817", "Context at depth 12, code 24623, node 267817",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 24623 and original node 267817, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
