using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0543Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0543.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0543",
        H("Original frontier context coverage 0543"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26067", "selected_cut_26067", "Selected cut at depth 13, code 354381, node 660054",
                "At remaining fuel 8 and original index 660054, selection on the full partial prefix of depth 13 and code 354381 returns the complete row with depth 13, base-four code 354381, original node 660054, kind 2, reserved field 0, 2261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26114", "selected_cut_26114", "Selected cut at depth 13, code 354431, node 661147",
                "At remaining fuel 8 and original index 661147, selection on the full partial prefix of depth 13 and code 354431 returns the complete row with depth 13, base-four code 354431, original node 661147, kind 2, reserved field 0, 1073 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88595-660086", "unmarked_context_12_88595_660086", "Unmarked parent at depth 12, code 88595",
                "The frontier Boolean is false at remaining fuel 9, original node 660086, the whole prefixCache at depth 12 and code 88595, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22151-661149", "unmarked_context_11_22151_661149", "Unmarked parent at depth 11, code 22151",
                "The frontier Boolean is false at remaining fuel 10, original node 661149, the whole prefixCache at depth 11 and code 22151, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88595-660086", "node_context_12_88595_660086", "Original split at fuel 9 and node 660086",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 660010, 660054, 660072, 660085. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22151-661149", "node_context_11_22151_661149", "Original split at fuel 10 and node 661149",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 660848, 660933, 661044, 661148. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-354381-660054", "context_13_354381_660054", "Context at depth 13, code 354381, node 660054",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354381 and original node 660054, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-22151-661149", "context_11_22151_661149", "Context at depth 11, code 22151, node 661149",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22151 and original node 661149, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_88604_660848, context_12_88605_660933, context_12_88606_661044, context_12_88607_661148.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
