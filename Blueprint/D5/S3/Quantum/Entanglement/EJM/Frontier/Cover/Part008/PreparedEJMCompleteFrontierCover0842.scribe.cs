using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0842Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0842.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0842",
        H("Original frontier context coverage 0842"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40419", "selected_cut_40419", "Selected cut at depth 12, code 309528, node 26677",
                "At remaining fuel 9 and original index 26677, selection on the full partial prefix of depth 12 and code 309528 returns the complete row with depth 12, base-four code 309528, original node 26677, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40466", "selected_cut_40466", "Selected cut at depth 9, code 4838, node 33466",
                "At remaining fuel 12 and original index 33466, selection on the full partial prefix of depth 9 and code 4838 returns the complete row with depth 9, base-four code 4838, original node 33466, kind 1, reserved field 0, 1 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77382-1099133", "unmarked_context_11_77382_1099133", "Unmarked parent at depth 11, code 77382",
                "The frontier Boolean is false at remaining fuel 10, original node 1099133, the whole prefixCache at depth 11 and code 77382, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4837-1100677", "unmarked_context_9_4837_1100677", "Unmarked parent at depth 9, code 4837",
                "The frontier Boolean is false at remaining fuel 12, original node 1100677, the whole prefixCache at depth 9 and code 4837, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77382-1099133", "node_context_11_77382_1099133", "Original split at fuel 10 and node 1099133",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 26677, 1099096, 3161, 1099132. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4837-1100677", "node_context_9_4837_1100677", "Original split at fuel 12 and node 1100677",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1100070, 893098, 1100393, 1100676. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-309528-26677", "context_12_309528_26677", "Context at depth 12, code 309528, node 26677",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 309528 and original node 26677, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-4838-33466", "context_9_4838_33466", "Context at depth 9, code 4838, node 33466",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 4838 and original node 33466, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
