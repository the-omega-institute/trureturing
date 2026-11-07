using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0926Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0926.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0926",
        H("Original frontier context coverage 0926"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44452", "selected_cut_44452", "Selected cut at depth 12, code 354160, node 1223107",
                "At remaining fuel 9 and original index 1223107, selection on the full partial prefix of depth 12 and code 354160 returns the complete row with depth 12, base-four code 354160, original node 1223107, kind 2, reserved field 0, 1529 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44498", "selected_cut_44498", "Selected cut at depth 12, code 354329, node 1224643",
                "At remaining fuel 9 and original index 1224643, selection on the full partial prefix of depth 12 and code 354329 returns the complete row with depth 12, base-four code 354329, original node 1224643, kind 2, reserved field 0, 2757 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22134-1223080", "unmarked_context_10_22134_1223080", "Unmarked parent at depth 10, code 22134",
                "The frontier Boolean is false at remaining fuel 11, original node 1223080, the whole prefixCache at depth 10 and code 22134, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88581-1224594", "unmarked_context_11_88581_1224594", "Unmarked parent at depth 11, code 88581",
                "The frontier Boolean is false at remaining fuel 10, original node 1224594, the whole prefixCache at depth 11 and code 88581, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22134-1223080", "node_context_10_22134_1223080", "Original split at fuel 11 and node 1223080",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1222952, 1222999, 1223038, 1223079. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88581-1224594", "node_context_11_88581_1224594", "Original split at fuel 10 and node 1224594",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1118965, 1224538, 1224593. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22134-1223080", "context_10_22134_1223080", "Context at depth 10, code 22134, node 1223080",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22134 and original node 1223080, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_88536_1222952, context_11_88537_1222999, context_11_88538_1223038, context_11_88539_1223079.", DescribeRole.Theorem),
            Node("context-12-354329-1224643", "context_12_354329_1224643", "Context at depth 12, code 354329, node 1224643",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354329 and original node 1224643, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
