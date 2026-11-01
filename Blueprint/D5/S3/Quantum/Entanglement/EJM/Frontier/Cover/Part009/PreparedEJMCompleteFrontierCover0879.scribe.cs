using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0879Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0879.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0879",
        H("Original frontier context coverage 0879"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42195", "selected_cut_42195", "Selected cut at depth 12, code 337482, node 893903",
                "At remaining fuel 9 and original index 893903, selection on the full partial prefix of depth 12 and code 337482 returns the complete row with depth 12, base-four code 337482, original node 893903, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42243", "selected_cut_42243", "Selected cut at depth 11, code 84399, node 1154619",
                "At remaining fuel 10 and original index 1154619, selection on the full partial prefix of depth 11 and code 84399 returns the complete row with depth 11, base-four code 84399, original node 1154619, kind 2, reserved field 0, 1425 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84370-1153361", "unmarked_context_11_84370_1153361", "Unmarked parent at depth 11, code 84370",
                "The frontier Boolean is false at remaining fuel 10, original node 1153361, the whole prefixCache at depth 11 and code 84370, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21098-1154509", "unmarked_context_10_21098_1154509", "Unmarked parent at depth 10, code 21098",
                "The frontier Boolean is false at remaining fuel 11, original node 1154509, the whole prefixCache at depth 10 and code 21098, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84370-1153361", "node_context_11_84370_1153361", "Original split at fuel 10 and node 1153361",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1153292, 1153320, 893903, 1153360. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21098-1154509", "node_context_10_21098_1154509", "Original split at fuel 11 and node 1154509",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1154451, 1154483, 1109453, 1154508. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-337482-893903", "context_12_337482_893903", "Context at depth 12, code 337482, node 893903",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337482 and original node 893903, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-84399-1154619", "context_11_84399_1154619", "Context at depth 11, code 84399, node 1154619",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84399 and original node 1154619, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
