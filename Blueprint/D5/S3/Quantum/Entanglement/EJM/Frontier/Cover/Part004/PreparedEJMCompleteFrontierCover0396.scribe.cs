using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0396Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0396.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0396",
        H("Original frontier context coverage 0396"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19011", "selected_cut_19011", "Selected cut at depth 13, code 287961, node 487459",
                "At remaining fuel 8 and original index 487459, selection on the full partial prefix of depth 13 and code 287961 returns the complete row with depth 13, base-four code 287961, original node 487459, kind 2, reserved field 0, 2949 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19057", "selected_cut_19057", "Selected cut at depth 13, code 288007, node 488530",
                "At remaining fuel 8 and original index 488530, selection on the full partial prefix of depth 13 and code 288007 returns the complete row with depth 13, base-four code 288007, original node 488530, kind 2, reserved field 0, 1141 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71990-487496", "unmarked_context_12_71990_487496", "Unmarked parent at depth 12, code 71990",
                "The frontier Boolean is false at remaining fuel 9, original node 487496, the whole prefixCache at depth 12 and code 71990, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72001-488531", "unmarked_context_12_72001_488531", "Unmarked parent at depth 12, code 72001",
                "The frontier Boolean is false at remaining fuel 9, original node 488531, the whole prefixCache at depth 12 and code 72001, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71990-487496", "node_context_12_71990_487496", "Original split at fuel 9 and node 487496",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 487426, 487459, 487485, 487495. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72001-488531", "node_context_12_72001_488531", "Original split at fuel 9 and node 488531",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 488498, 488520, 488530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-287961-487459", "context_13_287961_487459", "Context at depth 13, code 287961, node 487459",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 287961 and original node 487459, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72001-488531", "context_12_72001_488531", "Context at depth 12, code 72001, node 488531",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72001 and original node 488531, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_288004_3444, context_13_288005_488498, context_13_288006_488520, context_13_288007_488530.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
