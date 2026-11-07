using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0790Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0790.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0790",
        H("Original frontier context coverage 0790"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37923", "selected_cut_37923", "Selected cut at depth 12, code 300585, node 1017537",
                "At remaining fuel 9 and original index 1017537, selection on the full partial prefix of depth 12 and code 300585 returns the complete row with depth 12, base-four code 300585, original node 1017537, kind 2, reserved field 0, 3989 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37970", "selected_cut_37970", "Selected cut at depth 12, code 300647, node 1019847",
                "At remaining fuel 9 and original index 1019847, selection on the full partial prefix of depth 12 and code 300647 returns the complete row with depth 12, base-four code 300647, original node 1019847, kind 2, reserved field 0, 1949 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75146-1017603", "unmarked_context_11_75146_1017603", "Unmarked parent at depth 11, code 75146",
                "The frontier Boolean is false at remaining fuel 10, original node 1017603, the whole prefixCache at depth 11 and code 75146, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75161-1019848", "unmarked_context_11_75161_1019848", "Unmarked parent at depth 11, code 75161",
                "The frontier Boolean is false at remaining fuel 10, original node 1019848, the whole prefixCache at depth 11 and code 75161, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75146-1017603", "node_context_11_75146_1017603", "Original split at fuel 10 and node 1017603",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1017467, 1017537, 661671, 1017602. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75161-1019848", "node_context_11_75161_1019848", "Original split at fuel 10 and node 1019848",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1019778, 691709, 1019813, 1019847. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300585-1017537", "context_12_300585_1017537", "Context at depth 12, code 300585, node 1017537",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300585 and original node 1017537, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75161-1019848", "context_11_75161_1019848", "Context at depth 11, code 75161, node 1019848",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75161 and original node 1019848, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_300644_1019778, context_12_300645_691709, context_12_300646_1019813, context_12_300647_1019847.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
