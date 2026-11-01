using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0953Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0953.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0953",
        H("Original frontier context coverage 0953"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45747", "selected_cut_45747", "Selected cut at depth 12, code 368937, node 1271483",
                "At remaining fuel 9 and original index 1271483, selection on the full partial prefix of depth 12 and code 368937 returns the complete row with depth 12, base-four code 368937, original node 1271483, kind 2, reserved field 0, 2817 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45794", "selected_cut_45794", "Selected cut at depth 11, code 92255, node 1272952",
                "At remaining fuel 10 and original index 1272952, selection on the full partial prefix of depth 11 and code 92255 returns the complete row with depth 11, base-four code 92255, original node 1272952, kind 2, reserved field 0, 3185 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92234-1271528", "unmarked_context_11_92234_1271528", "Unmarked parent at depth 11, code 92234",
                "The frontier Boolean is false at remaining fuel 10, original node 1271528, the whole prefixCache at depth 11 and code 92234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23063-1272953", "unmarked_context_10_23063_1272953", "Unmarked parent at depth 10, code 23063",
                "The frontier Boolean is false at remaining fuel 11, original node 1272953, the whole prefixCache at depth 10 and code 23063, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92234-1271528", "node_context_11_92234_1271528", "Original split at fuel 10 and node 1271528",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1271483, 224365, 1271527. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23063-1272953", "node_context_10_23063_1272953", "Original split at fuel 11 and node 1272953",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1272795, 1272858, 1272902, 1272952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-368937-1271483", "context_12_368937_1271483", "Context at depth 12, code 368937, node 1271483",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368937 and original node 1271483, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23063-1272953", "context_10_23063_1272953", "Context at depth 10, code 23063, node 1272953",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23063 and original node 1272953, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_92252_1272795, context_11_92253_1272858, context_11_92254_1272902, context_11_92255_1272952.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
