using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0941Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0941.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0941",
        H("Original frontier context coverage 0941"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45172", "selected_cut_45172", "Selected cut at depth 11, code 89011, node 1248084",
                "At remaining fuel 10 and original index 1248084, selection on the full partial prefix of depth 11 and code 89011 returns the complete row with depth 11, base-four code 89011, original node 1248084, kind 2, reserved field 0, 1017 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45219", "selected_cut_45219", "Selected cut at depth 12, code 356148, node 1250420",
                "At remaining fuel 9 and original index 1250420, selection on the full partial prefix of depth 12 and code 356148 returns the complete row with depth 12, base-four code 356148, original node 1250420, kind 2, reserved field 0, 2429 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22252-1248085", "unmarked_context_10_22252_1248085", "Unmarked parent at depth 10, code 22252",
                "The frontier Boolean is false at remaining fuel 11, original node 1248085, the whole prefixCache at depth 10 and code 22252, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-89036-1250357", "unmarked_context_11_89036_1250357", "Unmarked parent at depth 11, code 89036",
                "The frontier Boolean is false at remaining fuel 10, original node 1250357, the whole prefixCache at depth 11 and code 89036, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22252-1248085", "node_context_10_22252_1248085", "Original split at fuel 11 and node 1248085",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1248015, 1248044, 1248067, 1248084. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-89036-1250357", "node_context_11_89036_1250357", "Original split at fuel 10 and node 1250357",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 399079, 1250242, 1250301, 1250356. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-89011-1248084", "context_11_89011_1248084", "Context at depth 11, code 89011, node 1248084",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 89011 and original node 1248084, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-356148-1250420", "context_12_356148_1250420", "Context at depth 12, code 356148, node 1250420",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 356148 and original node 1250420, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
