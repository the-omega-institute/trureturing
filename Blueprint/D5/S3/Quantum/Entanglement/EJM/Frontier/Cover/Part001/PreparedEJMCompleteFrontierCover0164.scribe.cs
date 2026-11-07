using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0164Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0164.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0164",
        H("Original frontier context coverage 0164"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07874", "selected_cut_07874", "Selected cut at depth 13, code 91142, node 225165",
                "At remaining fuel 8 and original index 225165, selection on the full partial prefix of depth 13 and code 91142 returns the complete row with depth 13, base-four code 91142, original node 225165, kind 2, reserved field 0, 2017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07922", "selected_cut_07922", "Selected cut at depth 13, code 91166, node 226357",
                "At remaining fuel 8 and original index 226357, selection on the full partial prefix of depth 13 and code 91166 returns the complete row with depth 13, base-four code 91166, original node 226357, kind 2, reserved field 0, 2077 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22785-225173", "unmarked_context_12_22785_225173", "Unmarked parent at depth 12, code 22785",
                "The frontier Boolean is false at remaining fuel 9, original node 225173, the whole prefixCache at depth 12 and code 22785, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-91164-226274", "unmarked_context_13_91164_226274", "Unmarked parent at depth 13, code 91164",
                "The frontier Boolean is false at remaining fuel 8, original node 226274, the whole prefixCache at depth 13 and code 91164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22785-225173", "node_context_12_22785_225173", "Original split at fuel 9 and node 225173",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 225127, 225147, 225165, 225172. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-91164-226274", "node_context_13_91164_226274", "Original split at fuel 8 and node 226274",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 226229, 226244, 226261, 226273. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-91142-225165", "context_13_91142_225165", "Context at depth 13, code 91142, node 225165",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91142 and original node 225165, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-91166-226357", "context_13_91166_226357", "Context at depth 13, code 91166, node 226357",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91166 and original node 226357, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
