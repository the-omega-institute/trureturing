using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0457Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0457.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0457",
        H("Original frontier context coverage 0457"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21939", "selected_cut_21939", "Selected cut at depth 13, code 301347, node 559874",
                "At remaining fuel 8 and original index 559874, selection on the full partial prefix of depth 13 and code 301347 returns the complete row with depth 13, base-four code 301347, original node 559874, kind 2, reserved field 0, 849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21987", "selected_cut_21987", "Selected cut at depth 13, code 301419, node 560796",
                "At remaining fuel 8 and original index 560796, selection on the full partial prefix of depth 13 and code 301419 returns the complete row with depth 13, base-four code 301419, original node 560796, kind 2, reserved field 0, 1645 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75336-559875", "unmarked_context_12_75336_559875", "Unmarked parent at depth 12, code 75336",
                "The frontier Boolean is false at remaining fuel 9, original node 559875, the whole prefixCache at depth 12 and code 75336, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18836-560581", "unmarked_context_11_18836_560581", "Unmarked parent at depth 11, code 18836",
                "The frontier Boolean is false at remaining fuel 10, original node 560581, the whole prefixCache at depth 11 and code 18836, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75336-559875", "node_context_12_75336_559875", "Original split at fuel 9 and node 559875",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 559847, 559868, 559874. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18836-560581", "node_context_11_18836_560581", "Original split at fuel 10 and node 560581",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 560411, 560460, 560511, 560580. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-301347-559874", "context_13_301347_559874", "Context at depth 13, code 301347, node 559874",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301347 and original node 559874, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-301419-560796", "context_13_301419_560796", "Context at depth 13, code 301419, node 560796",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 301419 and original node 560796, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
