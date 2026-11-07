using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0183Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0183.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0183",
        H("Original frontier context coverage 0183"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08787", "selected_cut_08787", "Selected cut at depth 13, code 92454, node 244943",
                "At remaining fuel 8 and original index 244943, selection on the full partial prefix of depth 13 and code 92454 returns the complete row with depth 13, base-four code 92454, original node 244943, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08834", "selected_cut_08834", "Selected cut at depth 13, code 92507, node 245915",
                "At remaining fuel 8 and original index 245915, selection on the full partial prefix of depth 13 and code 92507 returns the complete row with depth 13, base-four code 92507, original node 245915, kind 2, reserved field 0, 1121 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23113-244957", "unmarked_context_12_23113_244957", "Unmarked parent at depth 12, code 23113",
                "The frontier Boolean is false at remaining fuel 9, original node 244957, the whole prefixCache at depth 12 and code 23113, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23126-245916", "unmarked_context_12_23126_245916", "Unmarked parent at depth 12, code 23126",
                "The frontier Boolean is false at remaining fuel 9, original node 245916, the whole prefixCache at depth 12 and code 23126, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23113-244957", "node_context_12_23113_244957", "Original split at fuel 9 and node 244957",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 244918, 244943, 244956. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23126-245916", "node_context_12_23126_245916", "Original split at fuel 9 and node 245916",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 245884, 245901, 245915. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-92454-244943", "context_13_92454_244943", "Context at depth 13, code 92454, node 244943",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 92454 and original node 244943, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-23126-245916", "context_12_23126_245916", "Context at depth 12, code 23126, node 245916",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23126 and original node 245916, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_92504_3444, context_13_92505_245884, context_13_92506_245901, context_13_92507_245915.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
