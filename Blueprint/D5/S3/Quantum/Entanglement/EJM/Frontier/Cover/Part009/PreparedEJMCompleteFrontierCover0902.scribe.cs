using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0902Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0902.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0902",
        H("Original frontier context coverage 0902"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43300", "selected_cut_43300", "Selected cut at depth 12, code 339766, node 1184829",
                "At remaining fuel 9 and original index 1184829, selection on the full partial prefix of depth 12 and code 339766 returns the complete row with depth 12, base-four code 339766, original node 1184829, kind 2, reserved field 0, 2561 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43348", "selected_cut_43348", "Selected cut at depth 12, code 339835, node 1186042",
                "At remaining fuel 9 and original index 1186042, selection on the full partial prefix of depth 12 and code 339835 returns the complete row with depth 12, base-four code 339835, original node 1186042, kind 2, reserved field 0, 1253 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84941-1184879", "unmarked_context_11_84941_1184879", "Unmarked parent at depth 11, code 84941",
                "The frontier Boolean is false at remaining fuel 10, original node 1184879, the whole prefixCache at depth 11 and code 84941, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84957-1185965", "unmarked_context_11_84957_1185965", "Unmarked parent at depth 11, code 84957",
                "The frontier Boolean is false at remaining fuel 10, original node 1185965, the whole prefixCache at depth 11 and code 84957, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84941-1184879", "node_context_11_84941_1184879", "Original split at fuel 10 and node 1184879",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1184778, 1184829, 1184878. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84957-1185965", "node_context_11_84957_1185965", "Original split at fuel 10 and node 1185965",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1185896, 642794, 1185934, 1185964. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-339766-1184829", "context_12_339766_1184829", "Context at depth 12, code 339766, node 1184829",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339766 and original node 1184829, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-339835-1186042", "context_12_339835_1186042", "Context at depth 12, code 339835, node 1186042",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339835 and original node 1186042, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
