using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0109Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0109.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0109",
        H("Original frontier context coverage 0109"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05235", "selected_cut_05235", "Selected cut at depth 13, code 76953, node 162406",
                "At remaining fuel 8 and original index 162406, selection on the full partial prefix of depth 13 and code 76953 returns the complete row with depth 13, base-four code 76953, original node 162406, kind 2, reserved field 0, 2721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05282", "selected_cut_05282", "Selected cut at depth 13, code 77000, node 163567",
                "At remaining fuel 8 and original index 163567, selection on the full partial prefix of depth 13 and code 77000 returns the complete row with depth 13, base-four code 77000, original node 163567, kind 2, reserved field 0, 569 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-19238-162435", "unmarked_context_12_19238_162435", "Unmarked parent at depth 12, code 19238",
                "The frontier Boolean is false at remaining fuel 9, original node 162435, the whole prefixCache at depth 12 and code 19238, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-19249-163561", "unmarked_context_12_19249_163561", "Unmarked parent at depth 12, code 19249",
                "The frontier Boolean is false at remaining fuel 9, original node 163561, the whole prefixCache at depth 12 and code 19249, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-19238-162435", "node_context_12_19238_162435", "Original split at fuel 9 and node 162435",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 162361, 162406, 162425, 162434. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-19249-163561", "node_context_12_19249_163561", "Original split at fuel 9 and node 163561",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 163490, 163535, 163555, 163560. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-76953-162406", "context_13_76953_162406", "Context at depth 13, code 76953, node 162406",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 76953 and original node 162406, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-77000-163567", "context_13_77000_163567", "Context at depth 13, code 77000, node 163567",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 77000 and original node 163567, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
