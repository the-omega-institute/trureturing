using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0003Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0003.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0003",
        H("Original frontier context coverage 0003"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00145", "selected_cut_00145", "Selected cut at depth 13, code 1153, node 9092",
                "At remaining fuel 8 and original index 9092, selection on the full partial prefix of depth 13 and code 1153 returns the complete row with depth 13, base-four code 1153, original node 9092, kind 2, reserved field 0, 2649 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00193", "selected_cut_00193", "Selected cut at depth 13, code 1201, node 11251",
                "At remaining fuel 8 and original index 11251, selection on the full partial prefix of depth 13 and code 1201 returns the complete row with depth 13, base-four code 1201, original node 11251, kind 2, reserved field 0, 3829 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-288-9181", "unmarked_context_12_288_9181", "Unmarked parent at depth 12, code 288",
                "The frontier Boolean is false at remaining fuel 9, original node 9181, the whole prefixCache at depth 12 and code 288, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74-11126", "unmarked_context_11_74_11126", "Unmarked parent at depth 11, code 74",
                "The frontier Boolean is false at remaining fuel 10, original node 11126, the whole prefixCache at depth 11 and code 74, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-288-9181", "node_context_12_288_9181", "Original split at fuel 9 and node 9181",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 9035, 9092, 9149, 9180. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74-11126", "node_context_11_74_11126", "Original split at fuel 10 and node 11126",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 10744, 10872, 11002, 11125. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1153-9092", "context_13_1153_9092", "Context at depth 13, code 1153, node 9092",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1153 and original node 9092, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1201-11251", "context_13_1201_11251", "Context at depth 13, code 1201, node 11251",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1201 and original node 11251, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
