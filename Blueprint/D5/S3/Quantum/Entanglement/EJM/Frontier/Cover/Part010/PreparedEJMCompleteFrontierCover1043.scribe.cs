using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1043Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1043.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1043",
        H("Original frontier context coverage 1043"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50068", "selected_cut_50068", "Selected cut at depth 12, code 422944, node 435160",
                "At remaining fuel 9 and original index 435160, selection on the full partial prefix of depth 12 and code 422944 returns the complete row with depth 12, base-four code 422944, original node 435160, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50115", "selected_cut_50115", "Selected cut at depth 11, code 105807, node 1427500",
                "At remaining fuel 10 and original index 1427500, selection on the full partial prefix of depth 11 and code 105807 returns the complete row with depth 11, base-four code 105807, original node 1427500, kind 2, reserved field 0, 365 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-105735-1424380", "unmarked_context_11_105735_1424380", "Unmarked parent at depth 11, code 105735",
                "The frontier Boolean is false at remaining fuel 10, original node 1424380, the whole prefixCache at depth 11 and code 105735, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-105804-1427186", "unmarked_context_11_105804_1427186", "Unmarked parent at depth 11, code 105804",
                "The frontier Boolean is false at remaining fuel 10, original node 1427186, the whole prefixCache at depth 11 and code 105804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-105735-1424380", "node_context_11_105735_1424380", "Original split at fuel 10 and node 1424380",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1424309, 1424379, 517541. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-105804-1427186", "node_context_11_105804_1427186", "Original split at fuel 10 and node 1427186",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1416143, 1427074, 1427141, 1427185. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-105735-1424380", "context_11_105735_1424380", "Context at depth 11, code 105735, node 1424380",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 105735 and original node 1424380, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_422940_1415033, context_12_422941_1424309, context_12_422942_1424379, context_12_422943_517541.", DescribeRole.Theorem),
            Node("context-11-105807-1427500", "context_11_105807_1427500", "Context at depth 11, code 105807, node 1427500",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 105807 and original node 1427500, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
