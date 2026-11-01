using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0293Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0293.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0293",
        H("Original frontier context coverage 0293"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14068", "selected_cut_14068", "Selected cut at depth 12, code 27004, node 365266",
                "At remaining fuel 9 and original index 365266, selection on the full partial prefix of depth 12 and code 27004 returns the complete row with depth 12, base-four code 27004, original node 365266, kind 2, reserved field 0, 3181 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14115", "selected_cut_14115", "Selected cut at depth 12, code 27054, node 366345",
                "At remaining fuel 9 and original index 366345, selection on the full partial prefix of depth 12 and code 27054 returns the complete row with depth 12, base-four code 27054, original node 366345, kind 2, reserved field 0, 1369 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6750-365237", "unmarked_context_11_6750_365237", "Unmarked parent at depth 11, code 6750",
                "The frontier Boolean is false at remaining fuel 10, original node 365237, the whole prefixCache at depth 11 and code 6750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6761-366261", "unmarked_context_11_6761_366261", "Unmarked parent at depth 11, code 6761",
                "The frontier Boolean is false at remaining fuel 10, original node 366261, the whole prefixCache at depth 11 and code 6761, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6750-365237", "node_context_11_6750_365237", "Original split at fuel 10 and node 365237",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 365117, 365163, 365200, 365236. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6761-366261", "node_context_11_6761_366261", "Original split at fuel 10 and node 366261",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 366205, 366225, 366242, 366260. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6750-365237", "context_11_6750_365237", "Context at depth 11, code 6750, node 365237",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6750 and original node 365237, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_27000_365117, context_12_27001_365163, context_12_27002_365200, context_12_27003_365236.", DescribeRole.Theorem),
            Node("context-12-27054-366345", "context_12_27054_366345", "Context at depth 12, code 27054, node 366345",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27054 and original node 366345, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
