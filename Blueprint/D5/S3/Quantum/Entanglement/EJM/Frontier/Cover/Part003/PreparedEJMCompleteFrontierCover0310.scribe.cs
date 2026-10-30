using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0310Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0310.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0310",
        H("Original frontier context coverage 0310"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14885", "selected_cut_14885", "Selected cut at depth 13, code 109823, node 383022",
                "At remaining fuel 8 and original index 383022, selection on the full partial prefix of depth 13 and code 109823 returns the complete row with depth 13, base-four code 109823, original node 383022, kind 2, reserved field 0, 1101 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14931", "selected_cut_14931", "Selected cut at depth 13, code 109866, node 384143",
                "At remaining fuel 8 and original index 384143, selection on the full partial prefix of depth 13 and code 109866 returns the complete row with depth 13, base-four code 109866, original node 384143, kind 2, reserved field 0, 1781 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27455-383023", "unmarked_context_12_27455_383023", "Unmarked parent at depth 12, code 27455",
                "The frontier Boolean is false at remaining fuel 9, original node 383023, the whole prefixCache at depth 12 and code 27455, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27465-384089", "unmarked_context_12_27465_384089", "Unmarked parent at depth 12, code 27465",
                "The frontier Boolean is false at remaining fuel 9, original node 384089, the whole prefixCache at depth 12 and code 27465, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27455-383023", "node_context_12_27455_383023", "Original split at fuel 9 and node 383023",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 382901, 382971, 382997, 383022. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27465-384089", "node_context_12_27465_384089", "Original split at fuel 9 and node 384089",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 384037, 384065, 384088. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109823-383022", "context_13_109823_383022", "Context at depth 13, code 109823, node 383022",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109823 and original node 383022, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109866-384143", "context_13_109866_384143", "Context at depth 13, code 109866, node 384143",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109866 and original node 384143, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
