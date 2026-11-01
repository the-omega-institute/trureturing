using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0570Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0570.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0570",
        H("Original frontier context coverage 0570"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27364", "selected_cut_27364", "Selected cut at depth 12, code 91504, node 691936",
                "At remaining fuel 9 and original index 691936, selection on the full partial prefix of depth 12 and code 91504 returns the complete row with depth 12, base-four code 91504, original node 691936, kind 2, reserved field 0, 3177 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27410", "selected_cut_27410", "Selected cut at depth 12, code 91553, node 692988",
                "At remaining fuel 9 and original index 692988, selection on the full partial prefix of depth 12 and code 91553 returns the complete row with depth 12, base-four code 91553, original node 692988, kind 2, reserved field 0, 1301 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22875-691894", "unmarked_context_11_22875_691894", "Unmarked parent at depth 11, code 22875",
                "The frontier Boolean is false at remaining fuel 10, original node 691894, the whole prefixCache at depth 11 and code 22875, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5721-692954", "unmarked_context_10_5721_692954", "Unmarked parent at depth 10, code 5721",
                "The frontier Boolean is false at remaining fuel 11, original node 692954, the whole prefixCache at depth 10 and code 5721, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22875-691894", "node_context_11_22875_691894", "Original split at fuel 10 and node 691894",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 691821, 691822, 691855, 691893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5721-692954", "node_context_10_5721_692954", "Original split at fuel 11 and node 692954",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 692792, 692795, 692873, 692953. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-22875-691894", "context_11_22875_691894", "Context at depth 11, code 22875, node 691894",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22875 and original node 691894, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_91500_691821, context_12_91501_691822, context_12_91502_691855, context_12_91503_691893.", DescribeRole.Theorem),
            Node("context-12-91553-692988", "context_12_91553_692988", "Context at depth 12, code 91553, node 692988",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91553 and original node 692988, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
