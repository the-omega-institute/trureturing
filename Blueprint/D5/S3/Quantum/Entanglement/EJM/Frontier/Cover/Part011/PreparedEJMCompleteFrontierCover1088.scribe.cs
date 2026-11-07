using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1088Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1088.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1088",
        H("Original frontier context coverage 1088"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52226", "selected_cut_52226", "Selected cut at depth 11, code 288773, node 1468419",
                "At remaining fuel 10 and original index 1468419, selection on the full partial prefix of depth 11 and code 288773 returns the complete row with depth 11, base-four code 288773, original node 1468419, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52274", "selected_cut_52274", "Selected cut at depth 10, code 72227, node 1521111",
                "At remaining fuel 11 and original index 1521111, selection on the full partial prefix of depth 10 and code 72227 returns the complete row with depth 10, base-four code 72227, original node 1521111, kind 2, reserved field 0, 3301 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-72193-1518830", "unmarked_context_10_72193_1518830", "Unmarked parent at depth 10, code 72193",
                "The frontier Boolean is false at remaining fuel 11, original node 1518830, the whole prefixCache at depth 10 and code 72193, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-72226-1520969", "unmarked_context_10_72226_1520969", "Unmarked parent at depth 10, code 72226",
                "The frontier Boolean is false at remaining fuel 11, original node 1520969, the whole prefixCache at depth 10 and code 72226, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-72193-1518830", "node_context_10_72193_1518830", "Original split at fuel 11 and node 1518830",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1518654, 1468419, 1518754, 1518829. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-72226-1520969", "node_context_10_72226_1520969", "Original split at fuel 11 and node 1520969",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1520878, 1520923, 1468743, 1520968. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-288773-1468419", "context_11_288773_1468419", "Context at depth 11, code 288773, node 1468419",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 288773 and original node 1468419, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-72227-1521111", "context_10_72227_1521111", "Context at depth 10, code 72227, node 1521111",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72227 and original node 1521111, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
