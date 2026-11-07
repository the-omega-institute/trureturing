using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0314Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0314.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0314",
        H("Original frontier context coverage 0314"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15076", "selected_cut_15076", "Selected cut at depth 12, code 27544, node 387920",
                "At remaining fuel 9 and original index 387920, selection on the full partial prefix of depth 12 and code 27544 returns the complete row with depth 12, base-four code 27544, original node 387920, kind 2, reserved field 0, 1817 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15122", "selected_cut_15122", "Selected cut at depth 10, code 1727, node 388825",
                "At remaining fuel 11 and original index 388825, selection on the full partial prefix of depth 10 and code 1727 returns the complete row with depth 10, base-four code 1727, original node 388825, kind 2, reserved field 0, 1553 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6885-387902", "unmarked_context_11_6885_387902", "Unmarked parent at depth 11, code 6885",
                "The frontier Boolean is false at remaining fuel 10, original node 387902, the whole prefixCache at depth 11 and code 6885, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-431-388826", "unmarked_context_9_431_388826", "Unmarked parent at depth 9, code 431",
                "The frontier Boolean is false at remaining fuel 12, original node 388826, the whole prefixCache at depth 9 and code 431, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6885-387902", "node_context_11_6885_387902", "Original split at fuel 10 and node 387902",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 387835, 387854, 387881, 387901. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-431-388826", "node_context_9_431_388826", "Original split at fuel 12 and node 388826",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 388605, 388705, 388784, 388825. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6885-387902", "context_11_6885_387902", "Context at depth 11, code 6885, node 387902",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6885 and original node 387902, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_27540_387835, context_12_27541_387854, context_12_27542_387881, context_12_27543_387901.", DescribeRole.Theorem),
            Node("context-9-431-388826", "context_9_431_388826", "Context at depth 9, code 431, node 388826",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 431 and original node 388826, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1724_388605, context_10_1725_388705, context_10_1726_388784, context_10_1727_388825.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
