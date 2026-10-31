using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1040Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1040.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1040",
        H("Original frontier context coverage 1040"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49923", "selected_cut_49923", "Selected cut at depth 11, code 104901, node 892405",
                "At remaining fuel 10 and original index 892405, selection on the full partial prefix of depth 11 and code 104901 returns the complete row with depth 11, base-four code 104901, original node 892405, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49971", "selected_cut_49971", "Selected cut at depth 12, code 421146, node 1415270",
                "At remaining fuel 9 and original index 1415270, selection on the full partial prefix of depth 12 and code 421146 returns the complete row with depth 12, base-four code 421146, original node 1415270, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-104902-1417236", "unmarked_context_11_104902_1417236", "Unmarked parent at depth 11, code 104902",
                "The frontier Boolean is false at remaining fuel 10, original node 1417236, the whole prefixCache at depth 11 and code 104902, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-105284-1419159", "unmarked_context_11_105284_1419159", "Unmarked parent at depth 11, code 105284",
                "The frontier Boolean is false at remaining fuel 10, original node 1419159, the whole prefixCache at depth 11 and code 105284, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-104902-1417236", "node_context_11_104902_1417236", "Original split at fuel 10 and node 1417236",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1417096, 1417163, 1417235. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-105284-1419159", "node_context_11_105284_1419159", "Original split at fuel 10 and node 1419159",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1419026, 1419089, 1419158. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-104901-892405", "context_11_104901_892405", "Context at depth 11, code 104901, node 892405",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 104901 and original node 892405, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-421146-1415270", "context_12_421146_1415270", "Context at depth 12, code 421146, node 1415270",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 421146 and original node 1415270, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
