using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0035Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0035.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0035",
        H("Original frontier context coverage 0035"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01682", "selected_cut_01682", "Selected cut at depth 13, code 18764, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 18764 returns the complete row with depth 13, base-four code 18764, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01730", "selected_cut_01730", "Selected cut at depth 13, code 18809, node 59248",
                "At remaining fuel 8 and original index 59248, selection on the full partial prefix of depth 13 and code 18809 returns the complete row with depth 13, base-four code 18809, original node 59248, kind 2, reserved field 0, 1769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4691-58454", "unmarked_context_12_4691_58454", "Unmarked parent at depth 12, code 4691",
                "The frontier Boolean is false at remaining fuel 9, original node 58454, the whole prefixCache at depth 12 and code 4691, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4701-59229", "unmarked_context_12_4701_59229", "Unmarked parent at depth 12, code 4701",
                "The frontier Boolean is false at remaining fuel 9, original node 59229, the whole prefixCache at depth 12 and code 4701, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4691-58454", "node_context_12_4691_58454", "Original split at fuel 9 and node 58454",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 58413, 58434, 58453. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4701-59229", "node_context_12_4701_59229", "Original split at fuel 9 and node 59229",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 59169, 59203, 59228. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18764-3444", "context_13_18764_3444", "Context at depth 13, code 18764, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18764 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-18809-59248", "context_13_18809_59248", "Context at depth 13, code 18809, node 59248",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18809 and original node 59248, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
