using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0190Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0190.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0190",
        H("Original frontier context coverage 0190"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09124", "selected_cut_09124", "Selected cut at depth 14, code 372979, node 252787",
                "At remaining fuel 7 and original index 252787, selection on the full partial prefix of depth 14 and code 372979 returns the complete row with depth 14, base-four code 372979, original node 252787, kind 2, reserved field 0, 1525 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09170", "selected_cut_09170", "Selected cut at depth 13, code 93287, node 254137",
                "At remaining fuel 8 and original index 254137, selection on the full partial prefix of depth 13 and code 93287 returns the complete row with depth 13, base-four code 93287, original node 254137, kind 2, reserved field 0, 885 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-93244-252788", "unmarked_context_13_93244_252788", "Unmarked parent at depth 13, code 93244",
                "The frontier Boolean is false at remaining fuel 8, original node 252788, the whole prefixCache at depth 13 and code 93244, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23321-254138", "unmarked_context_12_23321_254138", "Unmarked parent at depth 12, code 23321",
                "The frontier Boolean is false at remaining fuel 9, original node 254138, the whole prefixCache at depth 12 and code 23321, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-93244-252788", "node_context_13_93244_252788", "Original split at fuel 8 and node 252788",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 252694, 252725, 252758, 252787. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23321-254138", "node_context_12_23321_254138", "Original split at fuel 9 and node 254138",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 254062, 254095, 254124, 254137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-372979-252787", "context_14_372979_252787", "Context at depth 14, code 372979, node 252787",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 372979 and original node 252787, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-23321-254138", "context_12_23321_254138", "Context at depth 12, code 23321, node 254138",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 23321 and original node 254138, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_93284_254062, context_13_93285_254095, context_13_93286_254124, context_13_93287_254137.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
