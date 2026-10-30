using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0132Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0132.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0132",
        H("Original frontier context coverage 0132"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06338", "selected_cut_06338", "Selected cut at depth 12, code 21524, node 190348",
                "At remaining fuel 9 and original index 190348, selection on the full partial prefix of depth 12 and code 21524 returns the complete row with depth 12, base-four code 21524, original node 190348, kind 2, reserved field 0, 3961 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06386", "selected_cut_06386", "Selected cut at depth 13, code 86171, node 191462",
                "At remaining fuel 8 and original index 191462, selection on the full partial prefix of depth 13 and code 86171 returns the complete row with depth 13, base-four code 86171, original node 191462, kind 2, reserved field 0, 889 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5380-190260", "unmarked_context_11_5380_190260", "Unmarked parent at depth 11, code 5380",
                "The frontier Boolean is false at remaining fuel 10, original node 190260, the whole prefixCache at depth 11 and code 5380, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21541-191388", "unmarked_context_12_21541_191388", "Unmarked parent at depth 12, code 21541",
                "The frontier Boolean is false at remaining fuel 9, original node 191388, the whole prefixCache at depth 12 and code 21541, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5380-190260", "node_context_11_5380_190260", "Original split at fuel 10 and node 190260",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 190141, 190185, 190259, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21541-191388", "node_context_12_21541_191388", "Original split at fuel 9 and node 191388",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 191338, 191362, 191378, 191387. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5380-190260", "context_11_5380_190260", "Context at depth 11, code 5380, node 190260",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5380 and original node 190260, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_21520_190141, context_12_21521_190185, context_12_21522_190259, context_12_21523_893.", DescribeRole.Theorem),
            Node("context-13-86171-191462", "context_13_86171_191462", "Context at depth 13, code 86171, node 191462",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 86171 and original node 191462, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
