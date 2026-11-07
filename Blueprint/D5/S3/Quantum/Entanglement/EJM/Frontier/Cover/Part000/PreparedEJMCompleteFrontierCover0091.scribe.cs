using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0091Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0091.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0091",
        H("Original frontier context coverage 0091"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04371", "selected_cut_04371", "Selected cut at depth 12, code 18444, node 4595",
                "At remaining fuel 9 and original index 4595, selection on the full partial prefix of depth 12 and code 18444 returns the complete row with depth 12, base-four code 18444, original node 4595, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04417", "selected_cut_04417", "Selected cut at depth 13, code 73831, node 141279",
                "At remaining fuel 8 and original index 141279, selection on the full partial prefix of depth 13 and code 73831 returns the complete row with depth 13, base-four code 73831, original node 141279, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18443-139529", "unmarked_context_12_18443_139529", "Unmarked parent at depth 12, code 18443",
                "The frontier Boolean is false at remaining fuel 9, original node 139529, the whole prefixCache at depth 12 and code 18443, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-18457-141280", "unmarked_context_12_18457_141280", "Unmarked parent at depth 12, code 18457",
                "The frontier Boolean is false at remaining fuel 9, original node 141280, the whole prefixCache at depth 12 and code 18457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18443-139529", "node_context_12_18443_139529", "Original split at fuel 9 and node 139529",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 139218, 139409, 139481, 139528. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-18457-141280", "node_context_12_18457_141280", "Original split at fuel 9 and node 141280",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 141197, 141252, 141272, 141279. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18443-139529", "context_12_18443_139529", "Context at depth 12, code 18443, node 139529",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18443 and original node 139529, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_73772_139218, context_13_73773_139409, context_13_73774_139481, context_13_73775_139528.", DescribeRole.Theorem),
            Node("context-12-18457-141280", "context_12_18457_141280", "Context at depth 12, code 18457, node 141280",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18457 and original node 141280, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_73828_141197, context_13_73829_141252, context_13_73830_141272, context_13_73831_141279.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
