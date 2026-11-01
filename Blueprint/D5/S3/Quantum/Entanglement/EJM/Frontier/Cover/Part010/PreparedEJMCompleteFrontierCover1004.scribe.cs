using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1004Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1004.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1004",
        H("Original frontier context coverage 1004"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48196", "selected_cut_48196", "Selected cut at depth 12, code 375568, node 1255011",
                "At remaining fuel 9 and original index 1255011, selection on the full partial prefix of depth 12 and code 375568 returns the complete row with depth 12, base-four code 375568, original node 1255011, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48243", "selected_cut_48243", "Selected cut at depth 12, code 375624, node 1352878",
                "At remaining fuel 9 and original index 1352878, selection on the full partial prefix of depth 12 and code 375624 returns the complete row with depth 12, base-four code 375624, original node 1352878, kind 2, reserved field 0, 1593 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23472-1351413", "unmarked_context_10_23472_1351413", "Unmarked parent at depth 10, code 23472",
                "The frontier Boolean is false at remaining fuel 11, original node 1351413, the whole prefixCache at depth 10 and code 23472, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93905-1352851", "unmarked_context_11_93905_1352851", "Unmarked parent at depth 11, code 93905",
                "The frontier Boolean is false at remaining fuel 10, original node 1352851, the whole prefixCache at depth 11 and code 93905, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23472-1351413", "node_context_10_23472_1351413", "Original split at fuel 11 and node 1351413",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1351165, 1351273, 1351412. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93905-1352851", "node_context_11_93905_1352851", "Original split at fuel 10 and node 1352851",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1352767, 1257136, 1352812, 1352850. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23472-1351413", "context_10_23472_1351413", "Context at depth 10, code 23472, node 1351413",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23472 and original node 1351413, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_93888_434745, context_11_93889_1351165, context_11_93890_1351273, context_11_93891_1351412.", DescribeRole.Theorem),
            Node("context-12-375624-1352878", "context_12_375624_1352878", "Context at depth 12, code 375624, node 1352878",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 375624 and original node 1352878, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
