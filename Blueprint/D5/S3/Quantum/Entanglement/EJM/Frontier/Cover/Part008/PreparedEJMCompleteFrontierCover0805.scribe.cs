using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0805Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0805.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0805",
        H("Original frontier context coverage 0805"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38643", "selected_cut_38643", "Selected cut at depth 13, code 1207332, node 1043468",
                "At remaining fuel 8 and original index 1043468, selection on the full partial prefix of depth 13 and code 1207332 returns the complete row with depth 13, base-four code 1207332, original node 1043468, kind 2, reserved field 0, 1385 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38691", "selected_cut_38691", "Selected cut at depth 12, code 301878, node 1045436",
                "At remaining fuel 9 and original index 1045436, selection on the full partial prefix of depth 12 and code 301878 returns the complete row with depth 12, base-four code 301878, original node 1045436, kind 2, reserved field 0, 2985 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-301833-1043511", "unmarked_context_12_301833_1043511", "Unmarked parent at depth 12, code 301833",
                "The frontier Boolean is false at remaining fuel 9, original node 1043511, the whole prefixCache at depth 12 and code 301833, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75468-1045262", "unmarked_context_11_75468_1045262", "Unmarked parent at depth 11, code 75468",
                "The frontier Boolean is false at remaining fuel 10, original node 1045262, the whole prefixCache at depth 11 and code 75468, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-301833-1043511", "node_context_12_301833_1043511", "Original split at fuel 9 and node 1043511",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1043468, 1043488, 1043506, 1043510. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75468-1045262", "node_context_11_75468_1045262", "Original split at fuel 10 and node 1045262",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1045117, 1045169, 1045216, 1045261. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1207332-1043468", "context_13_1207332_1043468", "Context at depth 13, code 1207332, node 1043468",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1207332 and original node 1043468, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301878-1045436", "context_12_301878_1045436", "Context at depth 12, code 301878, node 1045436",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301878 and original node 1045436, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
