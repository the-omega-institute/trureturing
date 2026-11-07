using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0362Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0362.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0362",
        H("Original frontier context coverage 0362"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17378", "selected_cut_17378", "Selected cut at depth 10, code 4376, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 4376 returns the complete row with depth 10, base-four code 4376, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17425", "selected_cut_17425", "Selected cut at depth 13, code 280660, node 443629",
                "At remaining fuel 8 and original index 443629, selection on the full partial prefix of depth 13 and code 280660 returns the complete row with depth 13, base-four code 280660, original node 443629, kind 2, reserved field 0, 2001 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-1093-442241", "unmarked_context_9_1093_442241", "Unmarked parent at depth 9, code 1093",
                "The frontier Boolean is false at remaining fuel 12, original node 442241, the whole prefixCache at depth 9 and code 1093, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-70164-443590", "unmarked_context_12_70164_443590", "Unmarked parent at depth 12, code 70164",
                "The frontier Boolean is false at remaining fuel 9, original node 443590, the whole prefixCache at depth 12 and code 70164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-1093-442241", "node_context_9_1093_442241", "Original split at fuel 12 and node 442241",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 3442, 441327, 442240, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-70164-443590", "node_context_12_70164_443590", "Original split at fuel 9 and node 443590",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 443473, 443541, 443571, 443589. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-1093-442241", "context_9_1093_442241", "Context at depth 9, code 1093, node 442241",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1093 and original node 442241, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_4372_3442, context_10_4373_441327, context_10_4374_442240, context_10_4375_3440.", DescribeRole.Theorem),
            Node("context-13-280660-443629", "context_13_280660_443629", "Context at depth 13, code 280660, node 443629",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 280660 and original node 443629, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
