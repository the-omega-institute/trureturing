using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0810Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0810.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0810",
        H("Original frontier context coverage 0810"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38883", "selected_cut_38883", "Selected cut at depth 12, code 302181, node 417109",
                "At remaining fuel 9 and original index 417109, selection on the full partial prefix of depth 12 and code 302181 returns the complete row with depth 12, base-four code 302181, original node 417109, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38931", "selected_cut_38931", "Selected cut at depth 11, code 75567, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 75567 returns the complete row with depth 11, base-four code 75567, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75545-1052486", "unmarked_context_11_75545_1052486", "Unmarked parent at depth 11, code 75545",
                "The frontier Boolean is false at remaining fuel 10, original node 1052486, the whole prefixCache at depth 11 and code 75545, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18890-1053685", "unmarked_context_10_18890_1053685", "Unmarked parent at depth 10, code 18890",
                "The frontier Boolean is false at remaining fuel 11, original node 1053685, the whole prefixCache at depth 10 and code 18890, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75545-1052486", "node_context_11_75545_1052486", "Original split at fuel 10 and node 1052486",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1052439, 417109, 1052462, 1052485. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18890-1053685", "node_context_10_18890_1053685", "Original split at fuel 11 and node 1053685",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1053536, 1053580, 1053630, 1053684. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302181-417109", "context_12_302181_417109", "Context at depth 12, code 302181, node 417109",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302181 and original node 417109, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75567-977886", "context_11_75567_977886", "Context at depth 11, code 75567, node 977886",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75567 and original node 977886, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
