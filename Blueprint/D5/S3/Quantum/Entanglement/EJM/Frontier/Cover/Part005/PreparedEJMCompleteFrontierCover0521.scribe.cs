using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0521Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0521.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0521",
        H("Original frontier context coverage 0521"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25012", "selected_cut_25012", "Selected cut at depth 12, code 77596, node 539296",
                "At remaining fuel 9 and original index 539296, selection on the full partial prefix of depth 12 and code 77596 returns the complete row with depth 12, base-four code 77596, original node 539296, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25059", "selected_cut_25059", "Selected cut at depth 13, code 310443, node 633824",
                "At remaining fuel 8 and original index 633824, selection on the full partial prefix of depth 13 and code 310443 returns the complete row with depth 13, base-four code 310443, original node 633824, kind 2, reserved field 0, 749 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19398-632659", "unmarked_context_11_19398_632659", "Unmarked parent at depth 11, code 19398",
                "The frontier Boolean is false at remaining fuel 10, original node 632659, the whole prefixCache at depth 11 and code 19398, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77610-633825", "unmarked_context_12_77610_633825", "Unmarked parent at depth 12, code 77610",
                "The frontier Boolean is false at remaining fuel 9, original node 633825, the whole prefixCache at depth 12 and code 77610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19398-632659", "node_context_11_19398_632659", "Original split at fuel 10 and node 632659",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 632285, 632426, 632550, 632658. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77610-633825", "node_context_12_77610_633825", "Original split at fuel 9 and node 633825",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 633753, 633793, 633818, 633824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19398-632659", "context_11_19398_632659", "Context at depth 11, code 19398, node 632659",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19398 and original node 632659, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77592_632285, context_12_77593_632426, context_12_77594_632550, context_12_77595_632658.", DescribeRole.Theorem),
            Node("context-12-77610-633825", "context_12_77610_633825", "Context at depth 12, code 77610, node 633825",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77610 and original node 633825, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_310440_633753, context_13_310441_633793, context_13_310442_633818, context_13_310443_633824.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
