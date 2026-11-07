using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0297Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0297.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0297",
        H("Original frontier context coverage 0297"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14259", "selected_cut_14259", "Selected cut at depth 13, code 108648, node 369786",
                "At remaining fuel 8 and original index 369786, selection on the full partial prefix of depth 13 and code 108648 returns the complete row with depth 13, base-four code 108648, original node 369786, kind 2, reserved field 0, 2441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14306", "selected_cut_14306", "Selected cut at depth 13, code 108695, node 370631",
                "At remaining fuel 8 and original index 370631, selection on the full partial prefix of depth 13 and code 108695 returns the complete row with depth 13, base-four code 108695, original node 370631, kind 2, reserved field 0, 781 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27162-369864", "unmarked_context_12_27162_369864", "Unmarked parent at depth 12, code 27162",
                "The frontier Boolean is false at remaining fuel 9, original node 369864, the whole prefixCache at depth 12 and code 27162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27173-370632", "unmarked_context_12_27173_370632", "Unmarked parent at depth 12, code 27173",
                "The frontier Boolean is false at remaining fuel 9, original node 370632, the whole prefixCache at depth 12 and code 27173, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27162-369864", "node_context_12_27162_369864", "Original split at fuel 9 and node 369864",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 369786, 369834, 369856, 369863. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27173-370632", "node_context_12_27173_370632", "Original split at fuel 9 and node 370632",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 370580, 370602, 370624, 370631. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108648-369786", "context_13_108648_369786", "Context at depth 13, code 108648, node 369786",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108648 and original node 369786, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27173-370632", "context_12_27173_370632", "Context at depth 12, code 27173, node 370632",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27173 and original node 370632, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_108692_370580, context_13_108693_370602, context_13_108694_370624, context_13_108695_370631.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
