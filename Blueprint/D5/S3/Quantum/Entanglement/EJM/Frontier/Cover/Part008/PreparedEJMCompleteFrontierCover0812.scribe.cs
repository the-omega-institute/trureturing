using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0812Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0812.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0812",
        H("Original frontier context coverage 0812"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38979", "selected_cut_38979", "Selected cut at depth 12, code 302373, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 302373 returns the complete row with depth 12, base-four code 302373, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39027", "selected_cut_39027", "Selected cut at depth 12, code 302439, node 1057585",
                "At remaining fuel 9 and original index 1057585, selection on the full partial prefix of depth 12 and code 302439 returns the complete row with depth 12, base-four code 302439, original node 1057585, kind 2, reserved field 0, 1977 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75593-1055910", "unmarked_context_11_75593_1055910", "Unmarked parent at depth 11, code 75593",
                "The frontier Boolean is false at remaining fuel 10, original node 1055910, the whole prefixCache at depth 11 and code 75593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75608-1057496", "unmarked_context_11_75608_1057496", "Unmarked parent at depth 11, code 75608",
                "The frontier Boolean is false at remaining fuel 10, original node 1057496, the whole prefixCache at depth 11 and code 75608, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75593-1055910", "node_context_11_75593_1055910", "Original split at fuel 10 and node 1055910",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1055797, 891951, 1055856, 1055909. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75608-1057496", "node_context_11_75608_1057496", "Original split at fuel 10 and node 1057496",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1057398, 1057436, 1057470, 1057495. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302373-891951", "context_12_302373_891951", "Context at depth 12, code 302373, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302373 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302439-1057585", "context_12_302439_1057585", "Context at depth 12, code 302439, node 1057585",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302439 and original node 1057585, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
