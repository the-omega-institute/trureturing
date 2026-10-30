using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0937Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0937.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0937",
        H("Original frontier context coverage 0937"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44979", "selected_cut_44979", "Selected cut at depth 12, code 355590, node 1241428",
                "At remaining fuel 9 and original index 1241428, selection on the full partial prefix of depth 12 and code 355590 returns the complete row with depth 12, base-four code 355590, original node 1241428, kind 2, reserved field 0, 2681 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45027", "selected_cut_45027", "Selected cut at depth 11, code 88911, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 88911 returns the complete row with depth 11, base-four code 88911, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88897-1241494", "unmarked_context_11_88897_1241494", "Unmarked parent at depth 11, code 88897",
                "The frontier Boolean is false at remaining fuel 10, original node 1241494, the whole prefixCache at depth 11 and code 88897, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88910-1243193", "unmarked_context_11_88910_1243193", "Unmarked parent at depth 11, code 88910",
                "The frontier Boolean is false at remaining fuel 10, original node 1243193, the whole prefixCache at depth 11 and code 88910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88897-1241494", "node_context_11_88897_1241494", "Original split at fuel 10 and node 1241494",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 1241428, 1241493. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88910-1243193", "node_context_11_88910_1243193", "Original split at fuel 10 and node 1243193",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1243082, 1243121, 1243162, 1243192. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-355590-1241428", "context_12_355590_1241428", "Context at depth 12, code 355590, node 1241428",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355590 and original node 1241428, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88911-977886", "context_11_88911_977886", "Context at depth 11, code 88911, node 977886",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88911 and original node 977886, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
