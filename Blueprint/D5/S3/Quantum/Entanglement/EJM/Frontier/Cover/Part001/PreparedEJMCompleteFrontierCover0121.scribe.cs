using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0121Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0121.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0121",
        H("Original frontier context coverage 0121"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05810", "selected_cut_05810", "Selected cut at depth 12, code 20888, node 177772",
                "At remaining fuel 9 and original index 177772, selection on the full partial prefix of depth 12 and code 20888 returns the complete row with depth 12, base-four code 20888, original node 177772, kind 2, reserved field 0, 1153 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05858", "selected_cut_05858", "Selected cut at depth 14, code 336038, node 179296",
                "At remaining fuel 7 and original index 179296, selection on the full partial prefix of depth 14 and code 336038 returns the complete row with depth 14, base-four code 336038, original node 179296, kind 2, reserved field 0, 1365 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5222-177829", "unmarked_context_11_5222_177829", "Unmarked parent at depth 11, code 5222",
                "The frontier Boolean is false at remaining fuel 10, original node 177829, the whole prefixCache at depth 11 and code 5222, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-84008-179190", "unmarked_context_13_84008_179190", "Unmarked parent at depth 13, code 84008",
                "The frontier Boolean is false at remaining fuel 8, original node 179190, the whole prefixCache at depth 13 and code 84008, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5222-177829", "node_context_11_5222_177829", "Original split at fuel 10 and node 177829",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 177772, 177790, 177807, 177828. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-84008-179190", "node_context_13_84008_179190", "Original split at fuel 8 and node 179190",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 179114, 179139, 179164, 179189. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20888-177772", "context_12_20888_177772", "Context at depth 12, code 20888, node 177772",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20888 and original node 177772, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-336038-179296", "context_14_336038_179296", "Context at depth 14, code 336038, node 179296",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 336038 and original node 179296, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
