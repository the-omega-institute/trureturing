using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0754Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0754.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0754",
        H("Original frontier context coverage 0754"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36195", "selected_cut_36195", "Selected cut at depth 12, code 288306, node 956833",
                "At remaining fuel 9 and original index 956833, selection on the full partial prefix of depth 12 and code 288306 returns the complete row with depth 12, base-four code 288306, original node 956833, kind 2, reserved field 0, 2725 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36242", "selected_cut_36242", "Selected cut at depth 12, code 288368, node 958410",
                "At remaining fuel 9 and original index 958410, selection on the full partial prefix of depth 12 and code 288368 returns the complete row with depth 12, base-four code 288368, original node 958410, kind 2, reserved field 0, 1945 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72076-956905", "unmarked_context_11_72076_956905", "Unmarked parent at depth 11, code 72076",
                "The frontier Boolean is false at remaining fuel 10, original node 956905, the whole prefixCache at depth 11 and code 72076, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18022-958374", "unmarked_context_10_18022_958374", "Unmarked parent at depth 10, code 18022",
                "The frontier Boolean is false at remaining fuel 11, original node 958374, the whole prefixCache at depth 10 and code 18022, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72076-956905", "node_context_11_72076_956905", "Original split at fuel 10 and node 956905",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 956751, 956786, 956833, 956904. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18022-958374", "node_context_10_18022_958374", "Original split at fuel 11 and node 958374",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 958083, 958173, 958245, 958373. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-288306-956833", "context_12_288306_956833", "Context at depth 12, code 288306, node 956833",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288306 and original node 956833, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-288368-958410", "context_12_288368_958410", "Context at depth 12, code 288368, node 958410",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288368 and original node 958410, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
