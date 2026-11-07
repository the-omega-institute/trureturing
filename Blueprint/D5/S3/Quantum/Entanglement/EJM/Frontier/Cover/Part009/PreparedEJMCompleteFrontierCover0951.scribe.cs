using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0951Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0951.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0951",
        H("Original frontier context coverage 0951"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45651", "selected_cut_45651", "Selected cut at depth 12, code 368691, node 1268203",
                "At remaining fuel 9 and original index 1268203, selection on the full partial prefix of depth 12 and code 368691 returns the complete row with depth 12, base-four code 368691, original node 1268203, kind 2, reserved field 0, 2085 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45698", "selected_cut_45698", "Selected cut at depth 11, code 92195, node 1269620",
                "At remaining fuel 10 and original index 1269620, selection on the full partial prefix of depth 11 and code 92195 returns the complete row with depth 11, base-four code 92195, original node 1269620, kind 2, reserved field 0, 1897 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92172-1268204", "unmarked_context_11_92172_1268204", "Unmarked parent at depth 11, code 92172",
                "The frontier Boolean is false at remaining fuel 10, original node 1268204, the whole prefixCache at depth 11 and code 92172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5761-1269487", "unmarked_context_9_5761_1269487", "Unmarked parent at depth 9, code 5761",
                "The frontier Boolean is false at remaining fuel 12, original node 1269487, the whole prefixCache at depth 9 and code 5761, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92172-1268204", "node_context_11_92172_1268204", "Original split at fuel 10 and node 1268204",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1268143, 1268171, 1268203. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5761-1269487", "node_context_9_5761_1269487", "Original split at fuel 12 and node 1269487",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1268897, 893098, 1269184, 1269486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-368691-1268203", "context_12_368691_1268203", "Context at depth 12, code 368691, node 1268203",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368691 and original node 1268203, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92195-1269620", "context_11_92195_1269620", "Context at depth 11, code 92195, node 1269620",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92195 and original node 1269620, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
