using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0374Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0374.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0374",
        H("Original frontier context coverage 0374"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17954", "selected_cut_17954", "Selected cut at depth 12, code 71000, node 459943",
                "At remaining fuel 9 and original index 459943, selection on the full partial prefix of depth 12 and code 71000 returns the complete row with depth 12, base-four code 71000, original node 459943, kind 2, reserved field 0, 3665 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18001", "selected_cut_18001", "Selected cut at depth 12, code 71176, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 71176 returns the complete row with depth 12, base-four code 71176, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17750-460092", "unmarked_context_11_17750_460092", "Unmarked parent at depth 11, code 17750",
                "The frontier Boolean is false at remaining fuel 10, original node 460092, the whole prefixCache at depth 11 and code 17750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17793-461676", "unmarked_context_11_17793_461676", "Unmarked parent at depth 11, code 17793",
                "The frontier Boolean is false at remaining fuel 10, original node 461676, the whole prefixCache at depth 11 and code 17793, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17750-460092", "node_context_11_17750_460092", "Original split at fuel 10 and node 460092",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 459943, 460000, 460041, 460091. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17793-461676", "node_context_11_17793_461676", "Original split at fuel 10 and node 461676",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 461391, 461526, 461675. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71000-459943", "context_12_71000_459943", "Context at depth 12, code 71000, node 459943",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71000 and original node 459943, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71176-448748", "context_12_71176_448748", "Context at depth 12, code 71176, node 448748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71176 and original node 448748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
