using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0839Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0839.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0839",
        H("Original frontier context coverage 0839"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40276", "selected_cut_40276", "Selected cut at depth 13, code 1236025, node 1094251",
                "At remaining fuel 8 and original index 1094251, selection on the full partial prefix of depth 13 and code 1236025 returns the complete row with depth 13, base-four code 1236025, original node 1094251, kind 2, reserved field 0, 1621 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40324", "selected_cut_40324", "Selected cut at depth 12, code 309055, node 762108",
                "At remaining fuel 9 and original index 762108, selection on the full partial prefix of depth 12 and code 309055 returns the complete row with depth 12, base-four code 309055, original node 762108, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-309006-1094275", "unmarked_context_12_309006_1094275", "Unmarked parent at depth 12, code 309006",
                "The frontier Boolean is false at remaining fuel 9, original node 1094275, the whole prefixCache at depth 12 and code 309006, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77262-1095971", "unmarked_context_11_77262_1095971", "Unmarked parent at depth 11, code 77262",
                "The frontier Boolean is false at remaining fuel 10, original node 1095971, the whole prefixCache at depth 11 and code 77262, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-309006-1094275", "node_context_12_309006_1094275", "Original split at fuel 9 and node 1094275",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1094224, 1094251, 1094267, 1094274. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77262-1095971", "node_context_11_77262_1095971", "Original split at fuel 10 and node 1095971",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1095851, 1095890, 1095931, 1095970. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1236025-1094251", "context_13_1236025_1094251", "Context at depth 13, code 1236025, node 1094251",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1236025 and original node 1094251, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-309055-762108", "context_12_309055_762108", "Context at depth 12, code 309055, node 762108",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 309055 and original node 762108, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
