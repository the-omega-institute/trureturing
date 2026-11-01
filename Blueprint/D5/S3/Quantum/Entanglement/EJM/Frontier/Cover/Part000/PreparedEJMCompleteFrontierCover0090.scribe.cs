using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0090Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0090.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0090",
        H("Original frontier context coverage 0090"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04322", "selected_cut_04322", "Selected cut at depth 13, code 73742, node 137540",
                "At remaining fuel 8 and original index 137540, selection on the full partial prefix of depth 13 and code 73742 returns the complete row with depth 13, base-four code 73742, original node 137540, kind 2, reserved field 0, 2809 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04370", "selected_cut_04370", "Selected cut at depth 13, code 73775, node 139528",
                "At remaining fuel 8 and original index 139528, selection on the full partial prefix of depth 13 and code 73775 returns the complete row with depth 13, base-four code 73775, original node 139528, kind 2, reserved field 0, 1445 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18435-137561", "unmarked_context_12_18435_137561", "Unmarked parent at depth 12, code 18435",
                "The frontier Boolean is false at remaining fuel 9, original node 137561, the whole prefixCache at depth 12 and code 18435, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-73773-139409", "unmarked_context_13_73773_139409", "Unmarked parent at depth 13, code 73773",
                "The frontier Boolean is false at remaining fuel 8, original node 139409, the whole prefixCache at depth 13 and code 73773, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18435-137561", "node_context_12_18435_137561", "Original split at fuel 9 and node 137561",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 137352, 137477, 137540, 137560. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-73773-139409", "node_context_13_73773_139409", "Original split at fuel 8 and node 139409",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 139264, 139321, 139368, 139408. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-73742-137540", "context_13_73742_137540", "Context at depth 13, code 73742, node 137540",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 73742 and original node 137540, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-73775-139528", "context_13_73775_139528", "Context at depth 13, code 73775, node 139528",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 73775 and original node 139528, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
