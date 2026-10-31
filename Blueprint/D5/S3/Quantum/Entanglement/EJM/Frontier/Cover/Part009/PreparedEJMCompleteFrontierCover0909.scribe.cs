using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0909Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0909.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0909",
        H("Original frontier context coverage 0909"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43635", "selected_cut_43635", "Selected cut at depth 11, code 87780, node 1196329",
                "At remaining fuel 10 and original index 1196329, selection on the full partial prefix of depth 11 and code 87780 returns the complete row with depth 11, base-four code 87780, original node 1196329, kind 2, reserved field 0, 3165 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43682", "selected_cut_43682", "Selected cut at depth 12, code 352298, node 474208",
                "At remaining fuel 9 and original index 474208, selection on the full partial prefix of depth 12 and code 352298 returns the complete row with depth 12, base-four code 352298, original node 474208, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21945-1196398", "unmarked_context_10_21945_1196398", "Unmarked parent at depth 10, code 21945",
                "The frontier Boolean is false at remaining fuel 11, original node 1196398, the whole prefixCache at depth 10 and code 21945, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88073-1197601", "unmarked_context_11_88073_1197601", "Unmarked parent at depth 11, code 88073",
                "The frontier Boolean is false at remaining fuel 10, original node 1197601, the whole prefixCache at depth 11 and code 88073, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21945-1196398", "node_context_10_21945_1196398", "Original split at fuel 11 and node 1196398",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1196329, 1192826, 1196369, 1196397. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88073-1197601", "node_context_11_88073_1197601", "Original split at fuel 10 and node 1197601",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1197509, 719134, 1197552, 1197600. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-87780-1196329", "context_11_87780_1196329", "Context at depth 11, code 87780, node 1196329",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 87780 and original node 1196329, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-352298-474208", "context_12_352298_474208", "Context at depth 12, code 352298, node 474208",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352298 and original node 474208, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
