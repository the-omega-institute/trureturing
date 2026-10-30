using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0851Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0851.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0851",
        H("Original frontier context coverage 0851"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40850", "selected_cut_40850", "Selected cut at depth 10, code 20807, node 3440",
                "At remaining fuel 11 and original index 3440, selection on the full partial prefix of depth 10 and code 20807 returns the complete row with depth 10, base-four code 20807, original node 3440, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40898", "selected_cut_40898", "Selected cut at depth 12, code 333359, node 1115799",
                "At remaining fuel 9 and original index 1115799, selection on the full partial prefix of depth 12 and code 333359 returns the complete row with depth 12, base-four code 333359, original node 1115799, kind 2, reserved field 0, 2609 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5201-1114188", "unmarked_context_9_5201_1114188", "Unmarked parent at depth 9, code 5201",
                "The frontier Boolean is false at remaining fuel 12, original node 1114188, the whole prefixCache at depth 9 and code 5201, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83339-1115800", "unmarked_context_11_83339_1115800", "Unmarked parent at depth 11, code 83339",
                "The frontier Boolean is false at remaining fuel 10, original node 1115800, the whole prefixCache at depth 11 and code 83339, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5201-1114188", "node_context_9_5201_1114188", "Original split at fuel 12 and node 1114188",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1113794, 893098, 1114187, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83339-1115800", "node_context_11_83339_1115800", "Original split at fuel 10 and node 1115800",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1115712, 1115760, 1115799. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-20807-3440", "context_10_20807_3440", "Context at depth 10, code 20807, node 3440",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 20807 and original node 3440, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-83339-1115800", "context_11_83339_1115800", "Context at depth 11, code 83339, node 1115800",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83339 and original node 1115800, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_333356_1108174, context_12_333357_1115712, context_12_333358_1115760, context_12_333359_1115799.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
