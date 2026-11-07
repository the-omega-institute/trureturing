using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0834Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0834.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0834",
        H("Original frontier context coverage 0834"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40036", "selected_cut_40036", "Selected cut at depth 12, code 308527, node 1087083",
                "At remaining fuel 9 and original index 1087083, selection on the full partial prefix of depth 12 and code 308527 returns the complete row with depth 12, base-four code 308527, original node 1087083, kind 2, reserved field 0, 3477 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40083", "selected_cut_40083", "Selected cut at depth 12, code 308589, node 1088529",
                "At remaining fuel 9 and original index 1088529, selection on the full partial prefix of depth 12 and code 308589 returns the complete row with depth 12, base-four code 308589, original node 1088529, kind 2, reserved field 0, 1765 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77131-1087084", "unmarked_context_11_77131_1087084", "Unmarked parent at depth 11, code 77131",
                "The frontier Boolean is false at remaining fuel 10, original node 1087084, the whole prefixCache at depth 11 and code 77131, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77146-1088475", "unmarked_context_11_77146_1088475", "Unmarked parent at depth 11, code 77146",
                "The frontier Boolean is false at remaining fuel 10, original node 1088475, the whole prefixCache at depth 11 and code 77146, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77131-1087084", "node_context_11_77131_1087084", "Original split at fuel 10 and node 1087084",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1086931, 1086971, 1087027, 1087083. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77146-1088475", "node_context_11_77146_1088475", "Original split at fuel 10 and node 1088475",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1088400, 1088436, 661671, 1088474. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-308527-1087083", "context_12_308527_1087083", "Context at depth 12, code 308527, node 1087083",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308527 and original node 1087083, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-308589-1088529", "context_12_308589_1088529", "Context at depth 12, code 308589, node 1088529",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308589 and original node 1088529, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
