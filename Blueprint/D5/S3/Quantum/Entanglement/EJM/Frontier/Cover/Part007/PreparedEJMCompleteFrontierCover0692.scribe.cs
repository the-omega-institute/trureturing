using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0692Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0692.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0692",
        H("Original frontier context coverage 0692"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33220", "selected_cut_33220", "Selected cut at depth 13, code 440461, node 855898",
                "At remaining fuel 8 and original index 855898, selection on the full partial prefix of depth 13 and code 440461 returns the complete row with depth 13, base-four code 440461, original node 855898, kind 2, reserved field 0, 2813 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33267", "selected_cut_33267", "Selected cut at depth 13, code 440511, node 856745",
                "At remaining fuel 8 and original index 856745, selection on the full partial prefix of depth 13 and code 440511 returns the complete row with depth 13, base-four code 440511, original node 856745, kind 2, reserved field 0, 893 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110115-855936", "unmarked_context_12_110115_855936", "Unmarked parent at depth 12, code 110115",
                "The frontier Boolean is false at remaining fuel 9, original node 855936, the whole prefixCache at depth 12 and code 110115, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27531-856747", "unmarked_context_11_27531_856747", "Unmarked parent at depth 11, code 27531",
                "The frontier Boolean is false at remaining fuel 10, original node 856747, the whole prefixCache at depth 11 and code 27531, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110115-855936", "node_context_12_110115_855936", "Original split at fuel 9 and node 855936",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 855856, 855898, 855929, 855935. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27531-856747", "node_context_11_27531_856747", "Original split at fuel 10 and node 856747",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 856518, 856605, 856659, 856746. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-440461-855898", "context_13_440461_855898", "Context at depth 13, code 440461, node 855898",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 440461 and original node 855898, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27531-856747", "context_11_27531_856747", "Context at depth 11, code 27531, node 856747",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27531 and original node 856747, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_110124_856518, context_12_110125_856605, context_12_110126_856659, context_12_110127_856746.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
