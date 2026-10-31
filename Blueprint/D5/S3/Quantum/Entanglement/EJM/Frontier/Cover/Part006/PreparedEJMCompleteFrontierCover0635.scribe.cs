using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0635Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0635.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0635",
        H("Original frontier context coverage 0635"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30483", "selected_cut_30483", "Selected cut at depth 13, code 418884, node 771876",
                "At remaining fuel 8 and original index 771876, selection on the full partial prefix of depth 13 and code 418884 returns the complete row with depth 13, base-four code 418884, original node 771876, kind 2, reserved field 0, 2129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30531", "selected_cut_30531", "Selected cut at depth 13, code 418938, node 773602",
                "At remaining fuel 8 and original index 773602, selection on the full partial prefix of depth 13 and code 418938 returns the complete row with depth 13, base-four code 418938, original node 773602, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104720-771831", "unmarked_context_12_104720_771831", "Unmarked parent at depth 12, code 104720",
                "The frontier Boolean is false at remaining fuel 9, original node 771831, the whole prefixCache at depth 12 and code 104720, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-104733-773489", "unmarked_context_12_104733_773489", "Unmarked parent at depth 12, code 104733",
                "The frontier Boolean is false at remaining fuel 9, original node 773489, the whole prefixCache at depth 12 and code 104733, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104720-771831", "node_context_12_104720_771831", "Original split at fuel 9 and node 771831",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 771748, 771785, 771818, 771830. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-104733-773489", "node_context_12_104733_773489", "Original split at fuel 9 and node 773489",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 773402, 773443, 773472, 773488. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-104720-771831", "context_12_104720_771831", "Context at depth 12, code 104720, node 771831",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104720 and original node 771831, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_418880_771748, context_13_418881_771785, context_13_418882_771818, context_13_418883_771830.", DescribeRole.Theorem),
            Node("context-13-418938-773602", "context_13_418938_773602", "Context at depth 13, code 418938, node 773602",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 418938 and original node 773602, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
