using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0018Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0018.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0018",
        H("Original frontier context coverage 0018"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00866", "selected_cut_00866", "Selected cut at depth 13, code 16427, node 35106",
                "At remaining fuel 8 and original index 35106, selection on the full partial prefix of depth 13 and code 16427 returns the complete row with depth 13, base-four code 16427, original node 35106, kind 2, reserved field 0, 901 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00912", "selected_cut_00912", "Selected cut at depth 12, code 4164, node 36738",
                "At remaining fuel 9 and original index 36738, selection on the full partial prefix of depth 12 and code 4164 returns the complete row with depth 12, base-four code 4164, original node 36738, kind 2, reserved field 0, 1541 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4106-35107", "unmarked_context_12_4106_35107", "Unmarked parent at depth 12, code 4106",
                "The frontier Boolean is false at remaining fuel 9, original node 35107, the whole prefixCache at depth 12 and code 4106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1040-36687", "unmarked_context_11_1040_36687", "Unmarked parent at depth 11, code 1040",
                "The frontier Boolean is false at remaining fuel 10, original node 36687, the whole prefixCache at depth 11 and code 1040, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4106-35107", "node_context_12_4106_35107", "Original split at fuel 9 and node 35107",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 35019, 35064, 35093, 35106. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1040-36687", "node_context_11_1040_36687", "Original split at fuel 10 and node 36687",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 36483, 36553, 36686, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-16427-35106", "context_13_16427_35106", "Context at depth 13, code 16427, node 35106",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 16427 and original node 35106, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-4164-36738", "context_12_4164_36738", "Context at depth 12, code 4164, node 36738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4164 and original node 36738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
