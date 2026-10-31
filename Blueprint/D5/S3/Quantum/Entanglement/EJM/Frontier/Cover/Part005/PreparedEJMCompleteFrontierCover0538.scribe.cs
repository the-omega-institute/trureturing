using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0538Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0538.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0538",
        H("Original frontier context coverage 0538"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25828", "selected_cut_25828", "Selected cut at depth 13, code 352510, node 653875",
                "At remaining fuel 8 and original index 653875, selection on the full partial prefix of depth 13 and code 352510 returns the complete row with depth 13, base-four code 352510, original node 653875, kind 2, reserved field 0, 1689 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25874", "selected_cut_25874", "Selected cut at depth 13, code 352610, node 655024",
                "At remaining fuel 8 and original index 655024, selection on the full partial prefix of depth 13 and code 352610 returns the complete row with depth 13, base-four code 352610, original node 655024, kind 2, reserved field 0, 1725 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88127-653880", "unmarked_context_12_88127_653880", "Unmarked parent at depth 12, code 88127",
                "The frontier Boolean is false at remaining fuel 9, original node 653880, the whole prefixCache at depth 12 and code 88127, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22037-654985", "unmarked_context_11_22037_654985", "Unmarked parent at depth 11, code 22037",
                "The frontier Boolean is false at remaining fuel 10, original node 654985, the whole prefixCache at depth 11 and code 22037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88127-653880", "node_context_12_88127_653880", "Original split at fuel 9 and node 653880",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 653793, 653848, 653875, 653879. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22037-654985", "node_context_11_22037_654985", "Original split at fuel 10 and node 654985",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 654884, 642341, 654928, 654984. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-352510-653875", "context_13_352510_653875", "Context at depth 13, code 352510, node 653875",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352510 and original node 653875, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-352610-655024", "context_13_352610_655024", "Context at depth 13, code 352610, node 655024",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 352610 and original node 655024, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
