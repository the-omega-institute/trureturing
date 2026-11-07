using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0564Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0564.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0564",
        H("Original frontier context coverage 0564"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27075", "selected_cut_27075", "Selected cut at depth 12, code 91284, node 685191",
                "At remaining fuel 9 and original index 685191, selection on the full partial prefix of depth 12 and code 91284 returns the complete row with depth 12, base-four code 91284, original node 685191, kind 2, reserved field 0, 781 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27122", "selected_cut_27122", "Selected cut at depth 11, code 22838, node 686220",
                "At remaining fuel 10 and original index 686220, selection on the full partial prefix of depth 11 and code 22838 returns the complete row with depth 11, base-four code 22838, original node 686220, kind 2, reserved field 0, 2193 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22820-685155", "unmarked_context_11_22820_685155", "Unmarked parent at depth 11, code 22820",
                "The frontier Boolean is false at remaining fuel 10, original node 685155, the whole prefixCache at depth 11 and code 22820, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5708-686159", "unmarked_context_10_5708_686159", "Unmarked parent at depth 10, code 5708",
                "The frontier Boolean is false at remaining fuel 11, original node 686159, the whole prefixCache at depth 10 and code 5708, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22820-685155", "node_context_11_22820_685155", "Original split at fuel 10 and node 685155",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 685077, 685103, 685131, 685154. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5708-686159", "node_context_10_5708_686159", "Original split at fuel 11 and node 686159",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 686062, 686089, 686123, 686158. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-22820-685155", "context_11_22820_685155", "Context at depth 11, code 22820, node 685155",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22820 and original node 685155, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_91280_685077, context_12_91281_685103, context_12_91282_685131, context_12_91283_685154.", DescribeRole.Theorem),
            Node("context-11-22838-686220", "context_11_22838_686220", "Context at depth 11, code 22838, node 686220",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22838 and original node 686220, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
