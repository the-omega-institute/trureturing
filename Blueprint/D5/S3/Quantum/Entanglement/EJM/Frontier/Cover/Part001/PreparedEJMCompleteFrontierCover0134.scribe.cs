using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0134Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0134.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0134",
        H("Original frontier context coverage 0134"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06434", "selected_cut_06434", "Selected cut at depth 12, code 21575, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 21575 returns the complete row with depth 12, base-four code 21575, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06481", "selected_cut_06481", "Selected cut at depth 13, code 86383, node 193409",
                "At remaining fuel 8 and original index 193409, selection on the full partial prefix of depth 13 and code 86383 returns the complete row with depth 13, base-four code 86383, original node 193409, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5393-192613", "unmarked_context_11_5393_192613", "Unmarked parent at depth 11, code 5393",
                "The frontier Boolean is false at remaining fuel 10, original node 192613, the whole prefixCache at depth 11 and code 5393, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5398-193411", "unmarked_context_11_5398_193411", "Unmarked parent at depth 11, code 5398",
                "The frontier Boolean is false at remaining fuel 10, original node 193411, the whole prefixCache at depth 11 and code 5398, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5393-192613", "node_context_11_5393_192613", "Original split at fuel 10 and node 192613",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 192456, 192544, 192612, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5398-193411", "node_context_11_5398_193411", "Original split at fuel 10 and node 193411",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 193237, 193298, 193357, 193410. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-21575-893", "context_12_21575_893", "Context at depth 12, code 21575, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21575 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5398-193411", "context_11_5398_193411", "Context at depth 11, code 5398, node 193411",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5398 and original node 193411, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_21592_193237, context_12_21593_193298, context_12_21594_193357, context_12_21595_193410.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
