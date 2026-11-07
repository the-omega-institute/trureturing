using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0326Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0326.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0326",
        H("Original frontier context coverage 0326"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15651", "selected_cut_15651", "Selected cut at depth 13, code 111657, node 401050",
                "At remaining fuel 8 and original index 401050, selection on the full partial prefix of depth 13 and code 111657 returns the complete row with depth 13, base-four code 111657, original node 401050, kind 2, reserved field 0, 4053 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15698", "selected_cut_15698", "Selected cut at depth 13, code 111698, node 402270",
                "At remaining fuel 8 and original index 402270, selection on the full partial prefix of depth 13 and code 111698 returns the complete row with depth 13, base-four code 111698, original node 402270, kind 2, reserved field 0, 1337 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27914-401104", "unmarked_context_12_27914_401104", "Unmarked parent at depth 12, code 27914",
                "The frontier Boolean is false at remaining fuel 9, original node 401104, the whole prefixCache at depth 12 and code 27914, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6980-402205", "unmarked_context_11_6980_402205", "Unmarked parent at depth 11, code 6980",
                "The frontier Boolean is false at remaining fuel 10, original node 402205, the whole prefixCache at depth 11 and code 6980, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27914-401104", "node_context_12_27914_401104", "Original split at fuel 9 and node 401104",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 400983, 401050, 401086, 401103. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6980-402205", "node_context_11_6980_402205", "Original split at fuel 10 and node 402205",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 401921, 401997, 402095, 402204. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111657-401050", "context_13_111657_401050", "Context at depth 13, code 111657, node 401050",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111657 and original node 401050, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111698-402270", "context_13_111698_402270", "Context at depth 13, code 111698, node 402270",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111698 and original node 402270, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
