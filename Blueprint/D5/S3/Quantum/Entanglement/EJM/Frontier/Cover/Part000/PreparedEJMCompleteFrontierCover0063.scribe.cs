using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0063Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0063.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0063",
        H("Original frontier context coverage 0063"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03028", "selected_cut_03028", "Selected cut at depth 14, code 107191, node 94104",
                "At remaining fuel 7 and original index 94104, selection on the full partial prefix of depth 14 and code 107191 returns the complete row with depth 14, base-four code 107191, original node 94104, kind 2, reserved field 0, 1333 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03073", "selected_cut_03073", "Selected cut at depth 13, code 26884, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 26884 returns the complete row with depth 13, base-four code 26884, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-26797-94105", "unmarked_context_13_26797_94105", "Unmarked parent at depth 13, code 26797",
                "The frontier Boolean is false at remaining fuel 8, original node 94105, the whole prefixCache at depth 13 and code 26797, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6720-95214", "unmarked_context_12_6720_95214", "Unmarked parent at depth 12, code 6720",
                "The frontier Boolean is false at remaining fuel 9, original node 95214, the whole prefixCache at depth 12 and code 6720, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-26797-94105", "node_context_13_26797_94105", "Original split at fuel 8 and node 94105",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 94002, 94045, 94078, 94104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6720-95214", "node_context_12_6720_95214", "Original split at fuel 9 and node 95214",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 95168, 95193, 95213. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-107191-94104", "context_14_107191_94104", "Context at depth 14, code 107191, node 94104",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 107191 and original node 94104, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-26884-3444", "context_13_26884_3444", "Context at depth 13, code 26884, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26884 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
