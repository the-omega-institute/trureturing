using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1030Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1030.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1030",
        H("Original frontier context coverage 1030"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49443", "selected_cut_49443", "Selected cut at depth 12, code 407586, node 1398773",
                "At remaining fuel 9 and original index 1398773, selection on the full partial prefix of depth 12 and code 407586 returns the complete row with depth 12, base-four code 407586, original node 1398773, kind 2, reserved field 0, 1669 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49490", "selected_cut_49490", "Selected cut at depth 12, code 407825, node 1400578",
                "At remaining fuel 9 and original index 1400578, selection on the full partial prefix of depth 12 and code 407825 returns the complete row with depth 12, base-four code 407825, original node 1400578, kind 2, reserved field 0, 2113 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101896-1398807", "unmarked_context_11_101896_1398807", "Unmarked parent at depth 11, code 101896",
                "The frontier Boolean is false at remaining fuel 10, original node 1398807, the whole prefixCache at depth 11 and code 101896, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1592-1400443", "unmarked_context_8_1592_1400443", "Unmarked parent at depth 8, code 1592",
                "The frontier Boolean is false at remaining fuel 13, original node 1400443, the whole prefixCache at depth 8 and code 1592, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101896-1398807", "node_context_11_101896_1398807", "Original split at fuel 10 and node 1398807",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1398733, 1398773, 1398806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1592-1400443", "node_context_8_1592_1400443", "Original split at fuel 13 and node 1400443",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1399314, 1399919, 1400313, 1400442. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-407586-1398773", "context_12_407586_1398773", "Context at depth 12, code 407586, node 1398773",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407586 and original node 1398773, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-407825-1400578", "context_12_407825_1400578", "Context at depth 12, code 407825, node 1400578",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407825 and original node 1400578, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
