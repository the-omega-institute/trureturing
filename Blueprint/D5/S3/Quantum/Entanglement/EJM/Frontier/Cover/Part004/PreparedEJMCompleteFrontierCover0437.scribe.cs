using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0437Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0437.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0437",
        H("Original frontier context coverage 0437"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20978", "selected_cut_20978", "Selected cut at depth 13, code 299060, node 538323",
                "At remaining fuel 8 and original index 538323, selection on the full partial prefix of depth 13 and code 299060 returns the complete row with depth 13, base-four code 299060, original node 538323, kind 2, reserved field 0, 917 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21026", "selected_cut_21026", "Selected cut at depth 13, code 299126, node 539375",
                "At remaining fuel 8 and original index 539375, selection on the full partial prefix of depth 13 and code 299126 returns the complete row with depth 13, base-four code 299126, original node 539375, kind 2, reserved field 0, 1485 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74765-538425", "unmarked_context_12_74765_538425", "Unmarked parent at depth 12, code 74765",
                "The frontier Boolean is false at remaining fuel 9, original node 538425, the whole prefixCache at depth 12 and code 74765, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18694-539295", "unmarked_context_11_18694_539295", "Unmarked parent at depth 11, code 18694",
                "The frontier Boolean is false at remaining fuel 10, original node 539295, the whole prefixCache at depth 11 and code 18694, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74765-538425", "node_context_12_74765_538425", "Original split at fuel 9 and node 538425",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 538323, 538378, 538424, 265883. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18694-539295", "node_context_11_18694_539295", "Original split at fuel 10 and node 539295",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 449505, 539129, 539202, 539294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-299060-538323", "context_13_299060_538323", "Context at depth 13, code 299060, node 538323",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299060 and original node 538323, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-299126-539375", "context_13_299126_539375", "Context at depth 13, code 299126, node 539375",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299126 and original node 539375, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
