using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0981Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0981.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0981",
        H("Original frontier context coverage 0981"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47092", "selected_cut_47092", "Selected cut at depth 10, code 23269, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 23269 returns the complete row with depth 10, base-four code 23269, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47139", "selected_cut_47139", "Selected cut at depth 12, code 372501, node 1172003",
                "At remaining fuel 9 and original index 1172003, selection on the full partial prefix of depth 12 and code 372501 returns the complete row with depth 12, base-four code 372501, original node 1172003, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23268-1316540", "unmarked_context_10_23268_1316540", "Unmarked parent at depth 10, code 23268",
                "The frontier Boolean is false at remaining fuel 11, original node 1316540, the whole prefixCache at depth 10 and code 23268, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93124-1318218", "unmarked_context_11_93124_1318218", "Unmarked parent at depth 11, code 93124",
                "The frontier Boolean is false at remaining fuel 10, original node 1318218, the whole prefixCache at depth 11 and code 93124, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23268-1316540", "node_context_10_23268_1316540", "Original split at fuel 11 and node 1316540",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1316252, 1316367, 1316427, 1316539. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93124-1318218", "node_context_11_93124_1318218", "Original split at fuel 10 and node 1318218",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1318092, 1318158, 1318217. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23268-1316540", "context_10_23268_1316540", "Context at depth 10, code 23268, node 1316540",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23268 and original node 1316540, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93072_1316252, context_11_93073_1316367, context_11_93074_1316427, context_11_93075_1316539.", DescribeRole.Theorem),
            Node("context-12-372501-1172003", "context_12_372501_1172003", "Context at depth 12, code 372501, node 1172003",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372501 and original node 1172003, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
