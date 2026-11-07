using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0665Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0665.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0665",
        H("Original frontier context coverage 0665"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31923", "selected_cut_31923", "Selected cut at depth 12, code 107619, node 819848",
                "At remaining fuel 9 and original index 819848, selection on the full partial prefix of depth 12 and code 107619 returns the complete row with depth 12, base-four code 107619, original node 819848, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31971", "selected_cut_31971", "Selected cut at depth 13, code 431151, node 821555",
                "At remaining fuel 8 and original index 821555, selection on the full partial prefix of depth 13 and code 431151 returns the complete row with depth 13, base-four code 431151, original node 821555, kind 2, reserved field 0, 1217 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26904-819849", "unmarked_context_11_26904_819849", "Unmarked parent at depth 11, code 26904",
                "The frontier Boolean is false at remaining fuel 10, original node 819849, the whole prefixCache at depth 11 and code 26904, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-431148-821328", "unmarked_context_13_431148_821328", "Unmarked parent at depth 13, code 431148",
                "The frontier Boolean is false at remaining fuel 8, original node 821328, the whole prefixCache at depth 13 and code 431148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26904-819849", "node_context_11_26904_819849", "Original split at fuel 10 and node 819849",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 819709, 819752, 819797, 819848. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-431148-821328", "node_context_13_431148_821328", "Original split at fuel 8 and node 821328",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 821245, 821261, 821299, 821327. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107619-819848", "context_12_107619_819848", "Context at depth 12, code 107619, node 819848",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107619 and original node 819848, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-431151-821555", "context_13_431151_821555", "Context at depth 13, code 431151, node 821555",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431151 and original node 821555, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
