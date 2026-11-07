using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0537Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0537.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0537",
        H("Original frontier context coverage 0537"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25779", "selected_cut_25779", "Selected cut at depth 13, code 352461, node 653003",
                "At remaining fuel 8 and original index 653003, selection on the full partial prefix of depth 13 and code 352461 returns the complete row with depth 13, base-four code 352461, original node 653003, kind 2, reserved field 0, 2541 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25827", "selected_cut_25827", "Selected cut at depth 13, code 352509, node 653848",
                "At remaining fuel 8 and original index 653848, selection on the full partial prefix of depth 13 and code 352509 returns the complete row with depth 13, base-four code 352509, original node 653848, kind 2, reserved field 0, 2809 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88115-653029", "unmarked_context_12_88115_653029", "Unmarked parent at depth 12, code 88115",
                "The frontier Boolean is false at remaining fuel 9, original node 653029, the whole prefixCache at depth 12 and code 88115, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88126-653790", "unmarked_context_12_88126_653790", "Unmarked parent at depth 12, code 88126",
                "The frontier Boolean is false at remaining fuel 9, original node 653790, the whole prefixCache at depth 12 and code 88126, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88115-653029", "node_context_12_88115_653029", "Original split at fuel 9 and node 653029",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 652965, 653003, 653024, 653028. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88126-653790", "node_context_12_88126_653790", "Original split at fuel 9 and node 653790",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 653728, 653760, 653784, 653789. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-352461-653003", "context_13_352461_653003", "Context at depth 13, code 352461, node 653003",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352461 and original node 653003, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-352509-653848", "context_13_352509_653848", "Context at depth 13, code 352509, node 653848",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352509 and original node 653848, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
