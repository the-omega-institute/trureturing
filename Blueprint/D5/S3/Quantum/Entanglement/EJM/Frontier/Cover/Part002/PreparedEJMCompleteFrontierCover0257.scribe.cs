using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0257Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0257.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0257",
        H("Original frontier context coverage 0257"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12339", "selected_cut_12339", "Selected cut at depth 13, code 104550, node 327081",
                "At remaining fuel 8 and original index 327081, selection on the full partial prefix of depth 13 and code 104550 returns the complete row with depth 13, base-four code 104550, original node 327081, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12386", "selected_cut_12386", "Selected cut at depth 13, code 104597, node 327857",
                "At remaining fuel 8 and original index 327857, selection on the full partial prefix of depth 13 and code 104597 returns the complete row with depth 13, base-four code 104597, original node 327857, kind 2, reserved field 0, 2089 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26137-327090", "unmarked_context_12_26137_327090", "Unmarked parent at depth 12, code 26137",
                "The frontier Boolean is false at remaining fuel 9, original node 327090, the whole prefixCache at depth 12 and code 26137, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26148-327822", "unmarked_context_12_26148_327822", "Unmarked parent at depth 12, code 26148",
                "The frontier Boolean is false at remaining fuel 9, original node 327822, the whole prefixCache at depth 12 and code 26148, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26137-327090", "node_context_12_26137_327090", "Original split at fuel 9 and node 327090",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 327036, 327063, 327081, 327089. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26148-327822", "node_context_12_26148_327822", "Original split at fuel 9 and node 327822",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 327783, 327806, 327817, 327821. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-104550-327081", "context_13_104550_327081", "Context at depth 13, code 104550, node 327081",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104550 and original node 327081, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-104597-327857", "context_13_104597_327857", "Context at depth 13, code 104597, node 327857",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104597 and original node 327857, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
