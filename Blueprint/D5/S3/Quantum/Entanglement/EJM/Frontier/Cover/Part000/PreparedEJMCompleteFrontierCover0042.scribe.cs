using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0042Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0042.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0042",
        H("Original frontier context coverage 0042"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02019", "selected_cut_02019", "Selected cut at depth 13, code 21675, node 67180",
                "At remaining fuel 8 and original index 67180, selection on the full partial prefix of depth 13 and code 21675 returns the complete row with depth 13, base-four code 21675, original node 67180, kind 2, reserved field 0, 913 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02065", "selected_cut_02065", "Selected cut at depth 13, code 21835, node 68177",
                "At remaining fuel 8 and original index 68177, selection on the full partial prefix of depth 13 and code 21835 returns the complete row with depth 13, base-four code 21835, original node 68177, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5418-67181", "unmarked_context_12_5418_67181", "Unmarked parent at depth 12, code 5418",
                "The frontier Boolean is false at remaining fuel 9, original node 67181, the whole prefixCache at depth 12 and code 5418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5458-68178", "unmarked_context_12_5458_68178", "Unmarked parent at depth 12, code 5458",
                "The frontier Boolean is false at remaining fuel 9, original node 68178, the whole prefixCache at depth 12 and code 5458, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5418-67181", "node_context_12_5418_67181", "Original split at fuel 9 and node 67181",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 67116, 67144, 67167, 67180. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5458-68178", "node_context_12_5458_68178", "Original split at fuel 9 and node 68178",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 68132, 68160, 68177. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-21675-67180", "context_13_21675_67180", "Context at depth 13, code 21675, node 67180",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 21675 and original node 67180, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-5458-68178", "context_12_5458_68178", "Context at depth 12, code 5458, node 68178",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5458 and original node 68178, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_21832_3444, context_13_21833_68132, context_13_21834_68160, context_13_21835_68177.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
