using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0840Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0840.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0840",
        H("Original frontier context coverage 0840"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40325", "selected_cut_40325", "Selected cut at depth 12, code 309056, node 1096119",
                "At remaining fuel 9 and original index 1096119, selection on the full partial prefix of depth 12 and code 309056 returns the complete row with depth 12, base-four code 309056, original node 1096119, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40372", "selected_cut_40372", "Selected cut at depth 12, code 309118, node 1097591",
                "At remaining fuel 9 and original index 1097591, selection on the full partial prefix of depth 12 and code 309118 returns the complete row with depth 12, base-four code 309118, original node 1097591, kind 2, reserved field 0, 1481 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77263-1096116", "unmarked_context_11_77263_1096116", "Unmarked parent at depth 11, code 77263",
                "The frontier Boolean is false at remaining fuel 10, original node 1096116, the whole prefixCache at depth 11 and code 77263, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77278-1097517", "unmarked_context_11_77278_1097517", "Unmarked parent at depth 11, code 77278",
                "The frontier Boolean is false at remaining fuel 10, original node 1097517, the whole prefixCache at depth 11 and code 77278, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77263-1096116", "node_context_11_77263_1096116", "Original split at fuel 10 and node 1096116",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1096025, 1096070, 1096115, 762108. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77278-1097517", "node_context_11_77278_1097517", "Original split at fuel 10 and node 1097517",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1097436, 1097458, 1097489, 1097516. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-77263-1096116", "context_11_77263_1096116", "Context at depth 11, code 77263, node 1096116",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 77263 and original node 1096116, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_309052_1096025, context_12_309053_1096070, context_12_309054_1096115, context_12_309055_762108.", DescribeRole.Theorem),
            Node("context-12-309118-1097591", "context_12_309118_1097591", "Context at depth 12, code 309118, node 1097591",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 309118 and original node 1097591, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
