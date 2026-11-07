using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0256Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0256.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0256",
        H("Original frontier context coverage 0256"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12291", "selected_cut_12291", "Selected cut at depth 13, code 104505, node 326020",
                "At remaining fuel 8 and original index 326020, selection on the full partial prefix of depth 13 and code 104505 returns the complete row with depth 13, base-four code 104505, original node 326020, kind 2, reserved field 0, 2961 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12338", "selected_cut_12338", "Selected cut at depth 13, code 104549, node 327063",
                "At remaining fuel 8 and original index 327063, selection on the full partial prefix of depth 13 and code 104549 returns the complete row with depth 13, base-four code 104549, original node 327063, kind 2, reserved field 0, 1565 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26126-326049", "unmarked_context_12_26126_326049", "Unmarked parent at depth 12, code 26126",
                "The frontier Boolean is false at remaining fuel 9, original node 326049, the whole prefixCache at depth 12 and code 26126, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26136-327012", "unmarked_context_12_26136_327012", "Unmarked parent at depth 12, code 26136",
                "The frontier Boolean is false at remaining fuel 9, original node 327012, the whole prefixCache at depth 12 and code 26136, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26126-326049", "node_context_12_26126_326049", "Original split at fuel 9 and node 326049",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 325976, 326020, 326040, 326048. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26136-327012", "node_context_12_26136_327012", "Original split at fuel 9 and node 327012",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 326972, 326993, 327006, 327011. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-104505-326020", "context_13_104505_326020", "Context at depth 13, code 104505, node 326020",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104505 and original node 326020, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104549-327063", "context_13_104549_327063", "Context at depth 13, code 104549, node 327063",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104549 and original node 327063, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
