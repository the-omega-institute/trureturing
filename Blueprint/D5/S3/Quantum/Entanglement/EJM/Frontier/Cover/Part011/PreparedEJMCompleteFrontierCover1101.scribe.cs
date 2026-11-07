using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1101Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1101.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1101",
        H("Original frontier context coverage 1101"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 25 context conclusions, 18 exact cut-selection equations, and 7 literal split equations paired with 7 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52849", "selected_cut_52849", "Selected cut at depth 4, code 19, node 891585",
                "At remaining fuel 17 and original index 891585, selection on the full partial prefix of depth 4 and code 19 returns the complete row with depth 4, base-four code 19, original node 891585, kind 1, reserved field 0, 1 subtree occurrences and completion domain 4294967296. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52866", "selected_cut_52866", "Selected cut at depth 1, code 3, node 1558775",
                "At remaining fuel 20 and original index 1558775, selection on the full partial prefix of depth 1 and code 3 returns the complete row with depth 1, base-four code 3, original node 1558775, kind 1, reserved field 0, 1 subtree occurrences and completion domain 274877906944. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-3-4-1557338", "unmarked_context_3_4_1557338", "Unmarked parent at depth 3, code 4",
                "The frontier Boolean is false at remaining fuel 18, original node 1557338, the whole prefixCache at depth 3 and code 4, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-0-0-1558776", "unmarked_context_0_0_1558776", "Unmarked parent at depth 0, code 0",
                "The frontier Boolean is false at remaining fuel 21, original node 1558776, the whole prefixCache at depth 0 and code 0, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-3-4-1557338", "node_context_3_4_1557338", "Original split at fuel 18 and node 1557338",
                "The complete original decoder output is the split at coordinate 3, with value children 0 through 3 respectively at original indices 1468245, 1537656, 1557337, 891585. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-0-0-1558776", "node_context_0_0_1558776", "Original split at fuel 21 and node 1558776",
                "The complete original decoder output is the split at coordinate 0, with value children 0 through 3 respectively at original indices 1558772, 1558773, 1558774, 1558775. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-4-19-891585", "context_4_19_891585", "Context at depth 4, code 19, node 891585",
                "The conclusion is adaptive Accepted at the exact depth 4, full base-four code 19 and original node 891585, hence remaining fuel 17, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-0-0-1558776", "context_0_0_1558776", "Context at depth 0, code 0, node 1558776",
                "The conclusion is adaptive Accepted at the exact depth 0, full base-four code 0 and original node 1558776, hence remaining fuel 21, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_1_0_1558772, context_1_1_1558773, context_1_2_1558774, context_1_3_1558775.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
