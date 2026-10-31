using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0178Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0178.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0178",
        H("Original frontier context coverage 0178"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08546", "selected_cut_08546", "Selected cut at depth 13, code 92225, node 239419",
                "At remaining fuel 8 and original index 239419, selection on the full partial prefix of depth 13 and code 92225 returns the complete row with depth 13, base-four code 92225, original node 239419, kind 2, reserved field 0, 2681 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08595", "selected_cut_08595", "Selected cut at depth 13, code 92271, node 240774",
                "At remaining fuel 8 and original index 240774, selection on the full partial prefix of depth 13 and code 92271 returns the complete row with depth 13, base-four code 92271, original node 240774, kind 2, reserved field 0, 1005 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23056-239449", "unmarked_context_12_23056_239449", "Unmarked parent at depth 12, code 23056",
                "The frontier Boolean is false at remaining fuel 9, original node 239449, the whole prefixCache at depth 12 and code 23056, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23066-240654", "unmarked_context_12_23066_240654", "Unmarked parent at depth 12, code 23066",
                "The frontier Boolean is false at remaining fuel 9, original node 240654, the whole prefixCache at depth 12 and code 23066, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23056-239449", "node_context_12_23056_239449", "Original split at fuel 9 and node 239449",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 239383, 239419, 239438, 239448. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23066-240654", "node_context_12_23066_240654", "Original split at fuel 9 and node 240654",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 240471, 240557, 240636, 240653. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-92225-239419", "context_13_92225_239419", "Context at depth 13, code 92225, node 239419",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92225 and original node 239419, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-92271-240774", "context_13_92271_240774", "Context at depth 13, code 92271, node 240774",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92271 and original node 240774, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
