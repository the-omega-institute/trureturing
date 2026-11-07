using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1015Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1015.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1015",
        H("Original frontier context coverage 1015"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48724", "selected_cut_48724", "Selected cut at depth 11, code 100687, node 1369425",
                "At remaining fuel 10 and original index 1369425, selection on the full partial prefix of depth 11 and code 100687 returns the complete row with depth 11, base-four code 100687, original node 1369425, kind 2, reserved field 0, 1657 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48771", "selected_cut_48771", "Selected cut at depth 12, code 403227, node 1371311",
                "At remaining fuel 9 and original index 1371311, selection on the full partial prefix of depth 12 and code 403227 returns the complete row with depth 12, base-four code 403227, original node 1371311, kind 2, reserved field 0, 2013 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-100686-1369383", "unmarked_context_11_100686_1369383", "Unmarked parent at depth 11, code 100686",
                "The frontier Boolean is false at remaining fuel 10, original node 1369383, the whole prefixCache at depth 11 and code 100686, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-100804-1371177", "unmarked_context_11_100804_1371177", "Unmarked parent at depth 11, code 100804",
                "The frontier Boolean is false at remaining fuel 10, original node 1371177, the whole prefixCache at depth 11 and code 100804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-100686-1369383", "node_context_11_100686_1369383", "Original split at fuel 10 and node 1369383",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1369301, 1369332, 1369382. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-100804-1371177", "node_context_11_100804_1371177", "Original split at fuel 10 and node 1371177",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1371035, 1371107, 1371176. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-100686-1369383", "context_11_100686_1369383", "Context at depth 11, code 100686, node 1369383",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 100686 and original node 1369383, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_402744_1108174, context_12_402745_1369301, context_12_402746_1369332, context_12_402747_1369382.", DescribeRole.Theorem),
            Node("context-12-403227-1371311", "context_12_403227_1371311", "Context at depth 12, code 403227, node 1371311",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 403227 and original node 1371311, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
