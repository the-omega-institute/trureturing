using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0156Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0156.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0156",
        H("Original frontier context coverage 0156"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07490", "selected_cut_07490", "Selected cut at depth 13, code 90257, node 217269",
                "At remaining fuel 8 and original index 217269, selection on the full partial prefix of depth 13 and code 90257 returns the complete row with depth 13, base-four code 90257, original node 217269, kind 2, reserved field 0, 2669 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07537", "selected_cut_07537", "Selected cut at depth 13, code 90304, node 218195",
                "At remaining fuel 8 and original index 218195, selection on the full partial prefix of depth 13 and code 90304 returns the complete row with depth 13, base-four code 90304, original node 218195, kind 2, reserved field 0, 889 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22564-217298", "unmarked_context_12_22564_217298", "Unmarked parent at depth 12, code 22564",
                "The frontier Boolean is false at remaining fuel 9, original node 217298, the whole prefixCache at depth 12 and code 22564, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1410-218181", "unmarked_context_10_1410_218181", "Unmarked parent at depth 10, code 1410",
                "The frontier Boolean is false at remaining fuel 11, original node 218181, the whole prefixCache at depth 10 and code 1410, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22564-217298", "node_context_12_22564_217298", "Original split at fuel 9 and node 217298",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 217224, 217269, 217287, 217297. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1410-218181", "node_context_10_1410_218181", "Original split at fuel 11 and node 218181",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 217213, 217520, 217882, 218180. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90257-217269", "context_13_90257_217269", "Context at depth 13, code 90257, node 217269",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90257 and original node 217269, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90304-218195", "context_13_90304_218195", "Context at depth 13, code 90304, node 218195",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90304 and original node 218195, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
