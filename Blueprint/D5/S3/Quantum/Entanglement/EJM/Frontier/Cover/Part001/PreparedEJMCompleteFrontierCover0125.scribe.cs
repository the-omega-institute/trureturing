using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0125Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0125.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0125",
        H("Original frontier context coverage 0125"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06003", "selected_cut_06003", "Selected cut at depth 13, code 84153, node 182674",
                "At remaining fuel 8 and original index 182674, selection on the full partial prefix of depth 13 and code 84153 returns the complete row with depth 13, base-four code 84153, original node 182674, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06051", "selected_cut_06051", "Selected cut at depth 14, code 336807, node 183476",
                "At remaining fuel 7 and original index 183476, selection on the full partial prefix of depth 14 and code 336807 returns the complete row with depth 14, base-four code 336807, original node 183476, kind 2, reserved field 0, 913 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21038-182701", "unmarked_context_12_21038_182701", "Unmarked parent at depth 12, code 21038",
                "The frontier Boolean is false at remaining fuel 9, original node 182701, the whole prefixCache at depth 12 and code 21038, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21049-183398", "unmarked_context_12_21049_183398", "Unmarked parent at depth 12, code 21049",
                "The frontier Boolean is false at remaining fuel 9, original node 183398, the whole prefixCache at depth 12 and code 21049, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21038-182701", "node_context_12_21038_182701", "Original split at fuel 9 and node 182701",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 182640, 182674, 182695, 182700. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21049-183398", "node_context_12_21049_183398", "Original split at fuel 9 and node 183398",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 183338, 183368, 183388, 183397. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84153-182674", "context_13_84153_182674", "Context at depth 13, code 84153, node 182674",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84153 and original node 182674, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-336807-183476", "context_14_336807_183476", "Context at depth 14, code 336807, node 183476",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 336807 and original node 183476, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
