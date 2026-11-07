using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0267Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0267.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0267",
        H("Original frontier context coverage 0267"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12819", "selected_cut_12819", "Selected cut at depth 13, code 105585, node 338340",
                "At remaining fuel 8 and original index 338340, selection on the full partial prefix of depth 13 and code 105585 returns the complete row with depth 13, base-four code 105585, original node 338340, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12866", "selected_cut_12866", "Selected cut at depth 13, code 105632, node 339237",
                "At remaining fuel 8 and original index 339237, selection on the full partial prefix of depth 13 and code 105632 returns the complete row with depth 13, base-four code 105632, original node 339237, kind 2, reserved field 0, 653 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26396-338362", "unmarked_context_12_26396_338362", "Unmarked parent at depth 12, code 26396",
                "The frontier Boolean is false at remaining fuel 9, original node 338362, the whole prefixCache at depth 12 and code 26396, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6601-339228", "unmarked_context_11_6601_339228", "Unmarked parent at depth 11, code 6601",
                "The frontier Boolean is false at remaining fuel 10, original node 339228, the whole prefixCache at depth 11 and code 6601, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26396-338362", "node_context_12_26396_338362", "Original split at fuel 9 and node 338362",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 338316, 338340, 338355, 338361. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6601-339228", "node_context_11_6601_339228", "Original split at fuel 10 and node 339228",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 339021, 339092, 339161, 339227. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105585-338340", "context_13_105585_338340", "Context at depth 13, code 105585, node 338340",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105585 and original node 338340, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-105632-339237", "context_13_105632_339237", "Context at depth 13, code 105632, node 339237",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105632 and original node 339237, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
