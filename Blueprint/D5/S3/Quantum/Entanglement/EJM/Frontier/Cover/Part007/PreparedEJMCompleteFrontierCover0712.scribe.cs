using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0712Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0712.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0712",
        H("Original frontier context coverage 0712"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34180", "selected_cut_34180", "Selected cut at depth 12, code 113005, node 883121",
                "At remaining fuel 9 and original index 883121, selection on the full partial prefix of depth 12 and code 113005 returns the complete row with depth 12, base-four code 113005, original node 883121, kind 2, reserved field 0, 2633 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34227", "selected_cut_34227", "Selected cut at depth 11, code 28266, node 479708",
                "At remaining fuel 10 and original index 479708, selection on the full partial prefix of depth 11 and code 28266 returns the complete row with depth 11, base-four code 28266, original node 479708, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-28251-883187", "unmarked_context_11_28251_883187", "Unmarked parent at depth 11, code 28251",
                "The frontier Boolean is false at remaining fuel 10, original node 883187, the whole prefixCache at depth 11 and code 28251, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-7065-884163", "unmarked_context_10_7065_884163", "Unmarked parent at depth 10, code 7065",
                "The frontier Boolean is false at remaining fuel 11, original node 884163, the whole prefixCache at depth 10 and code 7065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-28251-883187", "node_context_11_28251_883187", "Original split at fuel 10 and node 883187",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 883082, 883121, 883156, 883186. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-7065-884163", "node_context_10_7065_884163", "Original split at fuel 11 and node 884163",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 884017, 884051, 884105, 884162. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-113005-883121", "context_12_113005_883121", "Context at depth 12, code 113005, node 883121",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 113005 and original node 883121, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-28266-479708", "context_11_28266_479708", "Context at depth 11, code 28266, node 479708",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 28266 and original node 479708, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
