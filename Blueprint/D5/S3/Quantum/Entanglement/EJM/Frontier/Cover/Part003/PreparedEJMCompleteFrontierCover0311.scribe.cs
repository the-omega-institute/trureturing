using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0311Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0311.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0311",
        H("Original frontier context coverage 0311"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14932", "selected_cut_14932", "Selected cut at depth 13, code 109867, node 384154",
                "At remaining fuel 8 and original index 384154, selection on the full partial prefix of depth 13 and code 109867 returns the complete row with depth 13, base-four code 109867, original node 384154, kind 2, reserved field 0, 885 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14979", "selected_cut_14979", "Selected cut at depth 13, code 109926, node 385051",
                "At remaining fuel 8 and original index 385051, selection on the full partial prefix of depth 13 and code 109926 returns the complete row with depth 13, base-four code 109926, original node 385051, kind 2, reserved field 0, 2173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27466-384155", "unmarked_context_12_27466_384155", "Unmarked parent at depth 12, code 27466",
                "The frontier Boolean is false at remaining fuel 9, original node 384155, the whole prefixCache at depth 12 and code 27466, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6869-384950", "unmarked_context_11_6869_384950", "Unmarked parent at depth 11, code 6869",
                "The frontier Boolean is false at remaining fuel 10, original node 384950, the whole prefixCache at depth 11 and code 6869, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27466-384155", "node_context_12_27466_384155", "Original split at fuel 9 and node 384155",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 384121, 384143, 384154. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6869-384950", "node_context_11_6869_384950", "Original split at fuel 10 and node 384950",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 384834, 170504, 384903, 384949. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109867-384154", "context_13_109867_384154", "Context at depth 13, code 109867, node 384154",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109867 and original node 384154, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109926-385051", "context_13_109926_385051", "Context at depth 13, code 109926, node 385051",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109926 and original node 385051, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
