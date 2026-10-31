using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0440Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0440.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0440",
        H("Original frontier context coverage 0440"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21123", "selected_cut_21123", "Selected cut at depth 13, code 299244, node 540911",
                "At remaining fuel 8 and original index 540911, selection on the full partial prefix of depth 13 and code 299244 returns the complete row with depth 13, base-four code 299244, original node 540911, kind 2, reserved field 0, 213 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21170", "selected_cut_21170", "Selected cut at depth 13, code 299321, node 541832",
                "At remaining fuel 8 and original index 541832, selection on the full partial prefix of depth 13 and code 299321 returns the complete row with depth 13, base-four code 299321, original node 541832, kind 2, reserved field 0, 2033 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74811-540977", "unmarked_context_12_74811_540977", "Unmarked parent at depth 12, code 74811",
                "The frontier Boolean is false at remaining fuel 9, original node 540977, the whole prefixCache at depth 12 and code 74811, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18706-541717", "unmarked_context_11_18706_541717", "Unmarked parent at depth 11, code 18706",
                "The frontier Boolean is false at remaining fuel 10, original node 541717, the whole prefixCache at depth 11 and code 18706, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74811-540977", "node_context_12_74811_540977", "Original split at fuel 9 and node 540977",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 540911, 540940, 540966, 540976. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18706-541717", "node_context_11_18706_541717", "Original split at fuel 10 and node 541717",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 541548, 541601, 541658, 541716. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-299244-540911", "context_13_299244_540911", "Context at depth 13, code 299244, node 540911",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299244 and original node 540911, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-299321-541832", "context_13_299321_541832", "Context at depth 13, code 299321, node 541832",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 299321 and original node 541832, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
