using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0304Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0304.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0304",
        H("Original frontier context coverage 0304"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14595", "selected_cut_14595", "Selected cut at depth 12, code 27312, node 376185",
                "At remaining fuel 9 and original index 376185, selection on the full partial prefix of depth 12 and code 27312 returns the complete row with depth 12, base-four code 27312, original node 376185, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14643", "selected_cut_14643", "Selected cut at depth 14, code 438375, node 377329",
                "At remaining fuel 7 and original index 377329, selection on the full partial prefix of depth 14 and code 438375 returns the complete row with depth 14, base-four code 438375, original node 377329, kind 2, reserved field 0, 849 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6828-376220", "unmarked_context_11_6828_376220", "Unmarked parent at depth 11, code 6828",
                "The frontier Boolean is false at remaining fuel 10, original node 376220, the whole prefixCache at depth 11 and code 6828, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27397-377186", "unmarked_context_12_27397_377186", "Unmarked parent at depth 12, code 27397",
                "The frontier Boolean is false at remaining fuel 9, original node 377186, the whole prefixCache at depth 12 and code 27397, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6828-376220", "node_context_11_6828_376220", "Original split at fuel 10 and node 376220",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 376185, 376196, 376207, 376219. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27397-377186", "node_context_12_27397_377186", "Original split at fuel 9 and node 377186",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 377074, 377131, 377179, 377185. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27312-376185", "context_12_27312_376185", "Context at depth 12, code 27312, node 376185",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27312 and original node 376185, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-438375-377329", "context_14_438375_377329", "Context at depth 14, code 438375, node 377329",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 438375 and original node 377329, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
