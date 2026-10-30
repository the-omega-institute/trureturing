using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0761Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0761.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0761",
        H("Original frontier context coverage 0761"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36531", "selected_cut_36531", "Selected cut at depth 12, code 289410, node 968569",
                "At remaining fuel 9 and original index 968569, selection on the full partial prefix of depth 12 and code 289410 returns the complete row with depth 12, base-four code 289410, original node 968569, kind 2, reserved field 0, 1445 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36578", "selected_cut_36578", "Selected cut at depth 12, code 289553, node 970492",
                "At remaining fuel 9 and original index 970492, selection on the full partial prefix of depth 12 and code 289553 returns the complete row with depth 12, base-four code 289553, original node 970492, kind 2, reserved field 0, 3569 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72352-968599", "unmarked_context_11_72352_968599", "Unmarked parent at depth 11, code 72352",
                "The frontier Boolean is false at remaining fuel 10, original node 968599, the whole prefixCache at depth 11 and code 72352, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18096-970378", "unmarked_context_10_18096_970378", "Unmarked parent at depth 10, code 18096",
                "The frontier Boolean is false at remaining fuel 11, original node 970378, the whole prefixCache at depth 10 and code 18096, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72352-968599", "node_context_11_72352_968599", "Original split at fuel 10 and node 968599",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 290056, 968544, 968569, 968598. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18096-970378", "node_context_10_18096_970378", "Original split at fuel 11 and node 970378",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 969707, 969880, 970203, 970377. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-289410-968569", "context_12_289410_968569", "Context at depth 12, code 289410, node 968569",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289410 and original node 968569, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-289553-970492", "context_12_289553_970492", "Context at depth 12, code 289553, node 970492",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289553 and original node 970492, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
