using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0456Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0456.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0456",
        H("Original frontier context coverage 0456"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21892", "selected_cut_21892", "Selected cut at depth 13, code 301291, node 559136",
                "At remaining fuel 8 and original index 559136, selection on the full partial prefix of depth 13 and code 301291 returns the complete row with depth 13, base-four code 301291, original node 559136, kind 2, reserved field 0, 1313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21938", "selected_cut_21938", "Selected cut at depth 13, code 301346, node 559868",
                "At remaining fuel 8 and original index 559868, selection on the full partial prefix of depth 13 and code 301346 returns the complete row with depth 13, base-four code 301346, original node 559868, kind 2, reserved field 0, 1577 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75322-559137", "unmarked_context_12_75322_559137", "Unmarked parent at depth 12, code 75322",
                "The frontier Boolean is false at remaining fuel 9, original node 559137, the whole prefixCache at depth 12 and code 75322, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18833-559826", "unmarked_context_11_18833_559826", "Unmarked parent at depth 11, code 18833",
                "The frontier Boolean is false at remaining fuel 10, original node 559826, the whole prefixCache at depth 11 and code 18833, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75322-559137", "node_context_12_75322_559137", "Original split at fuel 9 and node 559137",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 559051, 559099, 559117, 559136. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18833-559826", "node_context_11_18833_559826", "Original split at fuel 10 and node 559826",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 559665, 559712, 559771, 559825. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-301291-559136", "context_13_301291_559136", "Context at depth 13, code 301291, node 559136",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301291 and original node 559136, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-301346-559868", "context_13_301346_559868", "Context at depth 13, code 301346, node 559868",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301346 and original node 559868, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
