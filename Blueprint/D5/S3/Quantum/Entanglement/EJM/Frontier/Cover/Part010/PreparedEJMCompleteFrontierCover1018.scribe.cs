using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1018Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1018.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1018",
        H("Original frontier context coverage 1018"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48867", "selected_cut_48867", "Selected cut at depth 10, code 25239, node 1375695",
                "At remaining fuel 11 and original index 1375695, selection on the full partial prefix of depth 10 and code 25239 returns the complete row with depth 10, base-four code 25239, original node 1375695, kind 2, reserved field 0, 2593 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48913", "selected_cut_48913", "Selected cut at depth 9, code 6319, node 1378651",
                "At remaining fuel 12 and original index 1378651, selection on the full partial prefix of depth 9 and code 6319 returns the complete row with depth 9, base-four code 6319, original node 1378651, kind 2, reserved field 0, 253 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6309-1375696", "unmarked_context_9_6309_1375696", "Unmarked parent at depth 9, code 6309",
                "The frontier Boolean is false at remaining fuel 12, original node 1375696, the whole prefixCache at depth 9 and code 6309, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-394-1378653", "unmarked_context_7_394_1378653", "Unmarked parent at depth 7, code 394",
                "The frontier Boolean is false at remaining fuel 14, original node 1378653, the whole prefixCache at depth 7 and code 394, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6309-1375696", "node_context_9_6309_1375696", "Original split at fuel 12 and node 1375696",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1375326, 893098, 1375533, 1375695. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-394-1378653", "node_context_7_394_1378653", "Original split at fuel 14 and node 1378653",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1364555, 1376083, 1366235, 1378652. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-25239-1375695", "context_10_25239_1375695", "Context at depth 10, code 25239, node 1375695",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25239 and original node 1375695, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-7-394-1378653", "context_7_394_1378653", "Context at depth 7, code 394, node 1378653",
                "The conclusion is adaptive Accepted at the exact depth 7, full base-four code 394 and original node 1378653, hence remaining fuel 14, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_8_1576_1364555, context_8_1577_1376083, context_8_1578_1366235, context_8_1579_1378652.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
