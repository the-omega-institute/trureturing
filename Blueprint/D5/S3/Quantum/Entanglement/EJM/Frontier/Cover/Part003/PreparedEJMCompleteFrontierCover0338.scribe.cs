using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0338Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0338.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0338",
        H("Original frontier context coverage 0338"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16228", "selected_cut_16228", "Selected cut at depth 13, code 112747, node 413829",
                "At remaining fuel 8 and original index 413829, selection on the full partial prefix of depth 13 and code 112747 returns the complete row with depth 13, base-four code 112747, original node 413829, kind 2, reserved field 0, 1145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16275", "selected_cut_16275", "Selected cut at depth 13, code 112794, node 414683",
                "At remaining fuel 8 and original index 414683, selection on the full partial prefix of depth 13 and code 112794 returns the complete row with depth 13, base-four code 112794, original node 414683, kind 2, reserved field 0, 1129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28186-413830", "unmarked_context_12_28186_413830", "Unmarked parent at depth 12, code 28186",
                "The frontier Boolean is false at remaining fuel 9, original node 413830, the whole prefixCache at depth 12 and code 28186, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28197-414633", "unmarked_context_12_28197_414633", "Unmarked parent at depth 12, code 28197",
                "The frontier Boolean is false at remaining fuel 9, original node 414633, the whole prefixCache at depth 12 and code 28197, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28186-413830", "node_context_12_28186_413830", "Original split at fuel 9 and node 413830",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 413731, 413798, 413822, 413829. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28197-414633", "node_context_12_28197_414633", "Original split at fuel 9 and node 414633",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 414583, 414608, 414623, 414632. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112747-413829", "context_13_112747_413829", "Context at depth 13, code 112747, node 413829",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112747 and original node 413829, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-112794-414683", "context_13_112794_414683", "Context at depth 13, code 112794, node 414683",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112794 and original node 414683, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
