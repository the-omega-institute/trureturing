using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0997Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0997.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0997",
        H("Original frontier context coverage 0997"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47860", "selected_cut_47860", "Selected cut at depth 12, code 374554, node 1340379",
                "At remaining fuel 9 and original index 1340379, selection on the full partial prefix of depth 12 and code 374554 returns the complete row with depth 12, base-four code 374554, original node 1340379, kind 2, reserved field 0, 2397 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47907", "selected_cut_47907", "Selected cut at depth 11, code 93657, node 1341760",
                "At remaining fuel 10 and original index 1341760, selection on the full partial prefix of depth 11 and code 93657 returns the complete row with depth 11, base-four code 93657, original node 1341760, kind 2, reserved field 0, 3717 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93638-1340426", "unmarked_context_11_93638_1340426", "Unmarked parent at depth 11, code 93638",
                "The frontier Boolean is false at remaining fuel 10, original node 1340426, the whole prefixCache at depth 11 and code 93638, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93656-1341700", "unmarked_context_11_93656_1341700", "Unmarked parent at depth 11, code 93656",
                "The frontier Boolean is false at remaining fuel 10, original node 1341700, the whole prefixCache at depth 11 and code 93656, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93638-1340426", "node_context_11_93638_1340426", "Original split at fuel 10 and node 1340426",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1340308, 1340338, 1340379, 1340425. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93656-1341700", "node_context_11_93656_1341700", "Original split at fuel 10 and node 1341700",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1341653, 1256866, 1341680, 1341699. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-374554-1340379", "context_12_374554_1340379", "Context at depth 12, code 374554, node 1340379",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 374554 and original node 1340379, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93657-1341760", "context_11_93657_1341760", "Context at depth 11, code 93657, node 1341760",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93657 and original node 1341760, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
