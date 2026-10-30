using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0167Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0167.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0167",
        H("Original frontier context coverage 0167"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08019", "selected_cut_08019", "Selected cut at depth 13, code 91248, node 228455",
                "At remaining fuel 8 and original index 228455, selection on the full partial prefix of depth 13 and code 91248 returns the complete row with depth 13, base-four code 91248, original node 228455, kind 2, reserved field 0, 1373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08066", "selected_cut_08066", "Selected cut at depth 13, code 91295, node 229383",
                "At remaining fuel 8 and original index 229383, selection on the full partial prefix of depth 13 and code 91295 returns the complete row with depth 13, base-four code 91295, original node 229383, kind 2, reserved field 0, 937 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5702-228435", "unmarked_context_11_5702_228435", "Unmarked parent at depth 11, code 5702",
                "The frontier Boolean is false at remaining fuel 10, original node 228435, the whole prefixCache at depth 11 and code 5702, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22823-229384", "unmarked_context_12_22823_229384", "Unmarked parent at depth 12, code 22823",
                "The frontier Boolean is false at remaining fuel 9, original node 229384, the whole prefixCache at depth 12 and code 22823, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5702-228435", "node_context_11_5702_228435", "Original split at fuel 10 and node 228435",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 228178, 228246, 228339, 228434. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22823-229384", "node_context_12_22823_229384", "Original split at fuel 9 and node 229384",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 229324, 229352, 229373, 229383. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5702-228435", "context_11_5702_228435", "Context at depth 11, code 5702, node 228435",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5702 and original node 228435, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22808_228178, context_12_22809_228246, context_12_22810_228339, context_12_22811_228434.", DescribeRole.Theorem),
            Node("context-12-22823-229384", "context_12_22823_229384", "Context at depth 12, code 22823, node 229384",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22823 and original node 229384, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_91292_229324, context_13_91293_229352, context_13_91294_229373, context_13_91295_229383.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
