using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1042Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1042.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1042",
        H("Original frontier context coverage 1042"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50020", "selected_cut_50020", "Selected cut at depth 12, code 421660, node 1415033",
                "At remaining fuel 9 and original index 1415033, selection on the full partial prefix of depth 12 and code 421660 returns the complete row with depth 12, base-four code 421660, original node 1415033, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50067", "selected_cut_50067", "Selected cut at depth 12, code 422943, node 517541",
                "At remaining fuel 9 and original index 517541, selection on the full partial prefix of depth 12 and code 422943 returns the complete row with depth 12, base-four code 422943, original node 517541, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-105415-1421922", "unmarked_context_11_105415_1421922", "Unmarked parent at depth 11, code 105415",
                "The frontier Boolean is false at remaining fuel 10, original node 1421922, the whole prefixCache at depth 11 and code 105415, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-105734-1424266", "unmarked_context_11_105734_1424266", "Unmarked parent at depth 11, code 105734",
                "The frontier Boolean is false at remaining fuel 10, original node 1424266, the whole prefixCache at depth 11 and code 105734, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-105415-1421922", "node_context_11_105415_1421922", "Original split at fuel 10 and node 1421922",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1421854, 1421921, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-105734-1424266", "node_context_11_105734_1424266", "Original split at fuel 10 and node 1424266",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1424198, 448662, 1424265. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-421660-1415033", "context_12_421660_1415033", "Context at depth 12, code 421660, node 1415033",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 421660 and original node 1415033, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-422943-517541", "context_12_422943_517541", "Context at depth 12, code 422943, node 517541",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 422943 and original node 517541, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
