using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0961Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0961.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0961",
        H("Original frontier context coverage 0961"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46130", "selected_cut_46130", "Selected cut at depth 11, code 92480, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 92480 returns the complete row with depth 11, base-four code 92480, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46178", "selected_cut_46178", "Selected cut at depth 11, code 92495, node 1286472",
                "At remaining fuel 10 and original index 1286472, selection on the full partial prefix of depth 11 and code 92495 returns the complete row with depth 11, base-four code 92495, original node 1286472, kind 2, reserved field 0, 3509 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92482-1284885", "unmarked_context_11_92482_1284885", "Unmarked parent at depth 11, code 92482",
                "The frontier Boolean is false at remaining fuel 10, original node 1284885, the whole prefixCache at depth 11 and code 92482, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23123-1286473", "unmarked_context_10_23123_1286473", "Unmarked parent at depth 10, code 23123",
                "The frontier Boolean is false at remaining fuel 11, original node 1286473, the whole prefixCache at depth 10 and code 23123, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92482-1284885", "node_context_11_92482_1284885", "Original split at fuel 10 and node 1284885",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1284740, 1284808, 1284884. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23123-1286473", "node_context_10_23123_1286473", "Original split at fuel 11 and node 1286473",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1286146, 1286268, 1286407, 1286472. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92480-434745", "context_11_92480_434745", "Context at depth 11, code 92480, node 434745",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92480 and original node 434745, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23123-1286473", "context_10_23123_1286473", "Context at depth 10, code 23123, node 1286473",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23123 and original node 1286473, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_92492_1286146, context_11_92493_1286268, context_11_92494_1286407, context_11_92495_1286472.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
