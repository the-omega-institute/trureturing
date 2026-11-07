using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0677Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0677.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0677",
        H("Original frontier context coverage 0677"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32499", "selected_cut_32499", "Selected cut at depth 13, code 438300, node 836181",
                "At remaining fuel 8 and original index 836181, selection on the full partial prefix of depth 13 and code 438300 returns the complete row with depth 13, base-four code 438300, original node 836181, kind 2, reserved field 0, 3613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32546", "selected_cut_32546", "Selected cut at depth 13, code 438371, node 837565",
                "At remaining fuel 8 and original index 837565, selection on the full partial prefix of depth 13 and code 438371 returns the complete row with depth 13, base-four code 438371, original node 837565, kind 2, reserved field 0, 553 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109575-836351", "unmarked_context_12_109575_836351", "Unmarked parent at depth 12, code 109575",
                "The frontier Boolean is false at remaining fuel 9, original node 836351, the whole prefixCache at depth 12 and code 109575, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-109592-837566", "unmarked_context_12_109592_837566", "Unmarked parent at depth 12, code 109592",
                "The frontier Boolean is false at remaining fuel 9, original node 837566, the whole prefixCache at depth 12 and code 109592, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109575-836351", "node_context_12_109575_836351", "Original split at fuel 9 and node 836351",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 836181, 836291, 836347, 836350. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-109592-837566", "node_context_12_109592_837566", "Original split at fuel 9 and node 837566",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 837484, 837517, 837557, 837565. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-438300-836181", "context_13_438300_836181", "Context at depth 13, code 438300, node 836181",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438300 and original node 836181, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109592-837566", "context_12_109592_837566", "Context at depth 12, code 109592, node 837566",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109592 and original node 837566, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_438368_837484, context_13_438369_837517, context_13_438370_837557, context_13_438371_837565.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
