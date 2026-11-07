using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0561Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0561.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0561",
        H("Original frontier context coverage 0561"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26930", "selected_cut_26930", "Selected cut at depth 12, code 91184, node 641337",
                "At remaining fuel 9 and original index 641337, selection on the full partial prefix of depth 12 and code 91184 returns the complete row with depth 12, base-four code 91184, original node 641337, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26979", "selected_cut_26979", "Selected cut at depth 13, code 364794, node 681964",
                "At remaining fuel 8 and original index 681964, selection on the full partial prefix of depth 13 and code 364794 returns the complete row with depth 13, base-four code 364794, original node 681964, kind 2, reserved field 0, 1257 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91185-680952", "unmarked_context_12_91185_680952", "Unmarked parent at depth 12, code 91185",
                "The frontier Boolean is false at remaining fuel 9, original node 680952, the whole prefixCache at depth 12 and code 91185, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91197-681912", "unmarked_context_12_91197_681912", "Unmarked parent at depth 12, code 91197",
                "The frontier Boolean is false at remaining fuel 9, original node 681912, the whole prefixCache at depth 12 and code 91197, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91185-680952", "node_context_12_91185_680952", "Original split at fuel 9 and node 680952",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 680896, 680922, 680944, 680951. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91197-681912", "node_context_12_91197_681912", "Original split at fuel 9 and node 681912",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 681832, 681882, 681905, 681911. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91184-641337", "context_12_91184_641337", "Context at depth 12, code 91184, node 641337",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91184 and original node 641337, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-364794-681964", "context_13_364794_681964", "Context at depth 13, code 364794, node 681964",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 364794 and original node 681964, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
