using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0317Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0317.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0317",
        H("Original frontier context coverage 0317"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15219", "selected_cut_15219", "Selected cut at depth 13, code 110700, node 391704",
                "At remaining fuel 8 and original index 391704, selection on the full partial prefix of depth 13 and code 110700 returns the complete row with depth 13, base-four code 110700, original node 391704, kind 2, reserved field 0, 1477 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15266", "selected_cut_15266", "Selected cut at depth 13, code 110747, node 392585",
                "At remaining fuel 8 and original index 392585, selection on the full partial prefix of depth 13 and code 110747 returns the complete row with depth 13, base-four code 110747, original node 392585, kind 2, reserved field 0, 833 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27675-391770", "unmarked_context_12_27675_391770", "Unmarked parent at depth 12, code 27675",
                "The frontier Boolean is false at remaining fuel 9, original node 391770, the whole prefixCache at depth 12 and code 27675, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27686-392586", "unmarked_context_12_27686_392586", "Unmarked parent at depth 12, code 27686",
                "The frontier Boolean is false at remaining fuel 9, original node 392586, the whole prefixCache at depth 12 and code 27686, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27675-391770", "node_context_12_27675_391770", "Original split at fuel 9 and node 391770",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 391704, 391739, 391760, 391769. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27686-392586", "node_context_12_27686_392586", "Original split at fuel 9 and node 392586",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 392536, 392558, 392573, 392585. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-110700-391704", "context_13_110700_391704", "Context at depth 13, code 110700, node 391704",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110700 and original node 391704, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27686-392586", "context_12_27686_392586", "Context at depth 12, code 27686, node 392586",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27686 and original node 392586, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_110744_392536, context_13_110745_392558, context_13_110746_392573, context_13_110747_392585.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
