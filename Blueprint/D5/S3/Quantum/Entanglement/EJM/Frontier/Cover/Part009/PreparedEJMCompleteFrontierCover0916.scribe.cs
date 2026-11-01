using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0916Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0916.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0916",
        H("Original frontier context coverage 0916"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43971", "selected_cut_43971", "Selected cut at depth 11, code 88233, node 1206494",
                "At remaining fuel 10 and original index 1206494, selection on the full partial prefix of depth 11 and code 88233 returns the complete row with depth 11, base-four code 88233, original node 1206494, kind 2, reserved field 0, 2085 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44019", "selected_cut_44019", "Selected cut at depth 12, code 353070, node 1208272",
                "At remaining fuel 9 and original index 1208272, selection on the full partial prefix of depth 12 and code 353070 returns the complete row with depth 12, base-four code 353070, original node 1208272, kind 2, reserved field 0, 2465 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22058-1206548", "unmarked_context_10_22058_1206548", "Unmarked parent at depth 10, code 22058",
                "The frontier Boolean is false at remaining fuel 11, original node 1206548, the whole prefixCache at depth 10 and code 22058, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88266-1208142", "unmarked_context_11_88266_1208142", "Unmarked parent at depth 11, code 88266",
                "The frontier Boolean is false at remaining fuel 10, original node 1208142, the whole prefixCache at depth 11 and code 88266, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22058-1206548", "node_context_10_22058_1206548", "Original split at fuel 11 and node 1206548",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1206453, 1206494, 1109453, 1206547. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88266-1208142", "node_context_11_88266_1208142", "Original split at fuel 10 and node 1208142",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1208049, 1208089, 474208, 1208141. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88233-1206494", "context_11_88233_1206494", "Context at depth 11, code 88233, node 1206494",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88233 and original node 1206494, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-353070-1208272", "context_12_353070_1208272", "Context at depth 12, code 353070, node 1208272",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353070 and original node 1208272, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
