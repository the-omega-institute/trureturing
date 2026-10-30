using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0404Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0404.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0404",
        H("Original frontier context coverage 0404"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19395", "selected_cut_19395", "Selected cut at depth 13, code 288813, node 495462",
                "At remaining fuel 8 and original index 495462, selection on the full partial prefix of depth 13 and code 288813 returns the complete row with depth 13, base-four code 288813, original node 495462, kind 2, reserved field 0, 3449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19442", "selected_cut_19442", "Selected cut at depth 13, code 288866, node 497311",
                "At remaining fuel 8 and original index 497311, selection on the full partial prefix of depth 13 and code 288866 returns the complete row with depth 13, base-four code 288866, original node 497311, kind 2, reserved field 0, 1845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72203-495494", "unmarked_context_12_72203_495494", "Unmarked parent at depth 12, code 72203",
                "The frontier Boolean is false at remaining fuel 9, original node 495494, the whole prefixCache at depth 12 and code 72203, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18053-497167", "unmarked_context_11_18053_497167", "Unmarked parent at depth 11, code 18053",
                "The frontier Boolean is false at remaining fuel 10, original node 497167, the whole prefixCache at depth 11 and code 18053, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72203-495494", "node_context_12_72203_495494", "Original split at fuel 9 and node 495494",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 495408, 495462, 495481, 495493. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18053-497167", "node_context_11_18053_497167", "Original split at fuel 10 and node 497167",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 496789, 496922, 497039, 497166. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288813-495462", "context_13_288813_495462", "Context at depth 13, code 288813, node 495462",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288813 and original node 495462, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-288866-497311", "context_13_288866_497311", "Context at depth 13, code 288866, node 497311",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288866 and original node 497311, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
