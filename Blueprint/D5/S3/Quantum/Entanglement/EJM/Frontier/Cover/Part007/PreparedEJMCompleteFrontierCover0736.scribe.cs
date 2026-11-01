using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0736Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0736.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0736",
        H("Original frontier context coverage 0736"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35331", "selected_cut_35331", "Selected cut at depth 11, code 71322, node 900587",
                "At remaining fuel 10 and original index 900587, selection on the full partial prefix of depth 11 and code 71322 returns the complete row with depth 11, base-four code 71322, original node 900587, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35378", "selected_cut_35378", "Selected cut at depth 12, code 285455, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 285455 returns the complete row with depth 12, base-four code 285455, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17830-927539", "unmarked_context_10_17830_927539", "Unmarked parent at depth 10, code 17830",
                "The frontier Boolean is false at remaining fuel 11, original node 927539, the whole prefixCache at depth 10 and code 17830, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71363-929516", "unmarked_context_11_71363_929516", "Unmarked parent at depth 11, code 71363",
                "The frontier Boolean is false at remaining fuel 10, original node 929516, the whole prefixCache at depth 11 and code 71363, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17830-927539", "node_context_10_17830_927539", "Original split at fuel 11 and node 927539",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 927407, 927453, 900587, 927538. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71363-929516", "node_context_11_71363_929516", "Original split at fuel 10 and node 929516",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 4596, 929450, 929515, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-71322-900587", "context_11_71322_900587", "Context at depth 11, code 71322, node 900587",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71322 and original node 900587, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-71363-929516", "context_11_71363_929516", "Context at depth 11, code 71363, node 929516",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71363 and original node 929516, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_285452_4596, context_12_285453_929450, context_12_285454_929515, context_12_285455_903806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
