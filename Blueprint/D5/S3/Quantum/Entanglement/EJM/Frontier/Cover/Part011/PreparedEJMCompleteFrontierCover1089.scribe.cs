using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1089Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1089.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1089",
        H("Original frontier context coverage 1089"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52275", "selected_cut_52275", "Selected cut at depth 10, code 72228, node 1521202",
                "At remaining fuel 11 and original index 1521202, selection on the full partial prefix of depth 10 and code 72228 returns the complete row with depth 10, base-four code 72228, original node 1521202, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52322", "selected_cut_52322", "Selected cut at depth 10, code 72263, node 1523235",
                "At remaining fuel 11 and original index 1523235, selection on the full partial prefix of depth 10 and code 72263 returns the complete row with depth 10, base-four code 72263, original node 1523235, kind 2, reserved field 0, 3185 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18056-1521112", "unmarked_context_9_18056_1521112", "Unmarked parent at depth 9, code 18056",
                "The frontier Boolean is false at remaining fuel 12, original node 1521112, the whole prefixCache at depth 9 and code 18056, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-18064-1522979", "unmarked_context_9_18064_1522979", "Unmarked parent at depth 9, code 18064",
                "The frontier Boolean is false at remaining fuel 12, original node 1522979, the whole prefixCache at depth 9 and code 18064, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18056-1521112", "node_context_9_18056_1521112", "Original split at fuel 12 and node 1521112",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1520785, 1520969, 1521111. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-18064-1522979", "node_context_9_18064_1522979", "Original split at fuel 12 and node 1522979",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1522714, 1522858, 1522978. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18056-1521112", "context_9_18056_1521112", "Context at depth 9, code 18056, node 1521112",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18056 and original node 1521112, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_72224_1468246, context_10_72225_1520785, context_10_72226_1520969, context_10_72227_1521111.", DescribeRole.Theorem),
            Node("context-10-72263-1523235", "context_10_72263_1523235", "Context at depth 10, code 72263, node 1523235",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72263 and original node 1523235, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
