using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0500Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0500.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0500",
        H("Original frontier context coverage 0500"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24004", "selected_cut_24004", "Selected cut at depth 13, code 307372, node 606474",
                "At remaining fuel 8 and original index 606474, selection on the full partial prefix of depth 13 and code 307372 returns the complete row with depth 13, base-four code 307372, original node 606474, kind 2, reserved field 0, 817 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24051", "selected_cut_24051", "Selected cut at depth 13, code 307431, node 607345",
                "At remaining fuel 8 and original index 607345, selection on the full partial prefix of depth 13 and code 307431 returns the complete row with depth 13, base-four code 307431, original node 607345, kind 2, reserved field 0, 845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76842-606457", "unmarked_context_12_76842_606457", "Unmarked parent at depth 12, code 76842",
                "The frontier Boolean is false at remaining fuel 9, original node 606457, the whole prefixCache at depth 12 and code 76842, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19213-607262", "unmarked_context_11_19213_607262", "Unmarked parent at depth 11, code 19213",
                "The frontier Boolean is false at remaining fuel 10, original node 607262, the whole prefixCache at depth 11 and code 19213, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76842-606457", "node_context_12_76842_606457", "Original split at fuel 9 and node 606457",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 606374, 606416, 606444, 606456. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19213-607262", "node_context_11_19213_607262", "Original split at fuel 10 and node 607262",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 475533, 607106, 607183, 607261. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76842-606457", "context_12_76842_606457", "Context at depth 12, code 76842, node 606457",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76842 and original node 606457, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_307368_606374, context_13_307369_606416, context_13_307370_606444, context_13_307371_606456.", DescribeRole.Theorem),
            Node("context-13-307431-607345", "context_13_307431_607345", "Context at depth 13, code 307431, node 607345",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 307431 and original node 607345, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
