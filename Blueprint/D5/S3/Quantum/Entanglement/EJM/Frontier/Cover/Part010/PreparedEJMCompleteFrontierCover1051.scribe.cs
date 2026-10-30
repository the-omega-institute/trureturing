using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1051Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1051.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1051",
        H("Original frontier context coverage 1051"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50452", "selected_cut_50452", "Selected cut at depth 11, code 106255, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 106255 returns the complete row with depth 11, base-four code 106255, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50498", "selected_cut_50498", "Selected cut at depth 11, code 106319, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 106319 returns the complete row with depth 11, base-four code 106319, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-26563-1441331", "unmarked_context_10_26563_1441331", "Unmarked parent at depth 10, code 26563",
                "The frontier Boolean is false at remaining fuel 11, original node 1441331, the whole prefixCache at depth 10 and code 26563, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6644-1443332", "unmarked_context_9_6644_1443332", "Unmarked parent at depth 9, code 6644",
                "The frontier Boolean is false at remaining fuel 12, original node 1443332, the whole prefixCache at depth 9 and code 6644, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-26563-1441331", "node_context_10_26563_1441331", "Original split at fuel 11 and node 1441331",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1441177, 1441265, 1441330, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6644-1443332", "node_context_9_6644_1443332", "Original split at fuel 12 and node 1443332",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1442392, 1442692, 1443066, 1443331. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-106255-977886", "context_11_106255_977886", "Context at depth 11, code 106255, node 977886",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106255 and original node 977886, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-6644-1443332", "context_9_6644_1443332", "Context at depth 9, code 6644, node 1443332",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6644 and original node 1443332, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_26576_1442392, context_10_26577_1442692, context_10_26578_1443066, context_10_26579_1443331.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
