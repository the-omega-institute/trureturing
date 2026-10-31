using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0980Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0980.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0980",
        H("Original frontier context coverage 0980"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47044", "selected_cut_47044", "Selected cut at depth 12, code 372244, node 1314850",
                "At remaining fuel 9 and original index 1314850, selection on the full partial prefix of depth 12 and code 372244 returns the complete row with depth 12, base-four code 372244, original node 1314850, kind 2, reserved field 0, 3625 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47091", "selected_cut_47091", "Selected cut at depth 12, code 372303, node 1316538",
                "At remaining fuel 9 and original index 1316538, selection on the full partial prefix of depth 12 and code 372303 returns the complete row with depth 12, base-four code 372303, original node 1316538, kind 2, reserved field 0, 1537 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93060-1314778", "unmarked_context_11_93060_1314778", "Unmarked parent at depth 11, code 93060",
                "The frontier Boolean is false at remaining fuel 10, original node 1314778, the whole prefixCache at depth 11 and code 93060, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93075-1316539", "unmarked_context_11_93075_1316539", "Unmarked parent at depth 11, code 93075",
                "The frontier Boolean is false at remaining fuel 10, original node 1316539, the whole prefixCache at depth 11 and code 93075, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93060-1314778", "node_context_11_93060_1314778", "Original split at fuel 10 and node 1314778",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1314660, 1314715, 1314777. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93075-1316539", "node_context_11_93075_1316539", "Original split at fuel 10 and node 1316539",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1316459, 1316484, 1316509, 1316538. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93060-1314778", "context_11_93060_1314778", "Context at depth 11, code 93060, node 1314778",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93060 and original node 1314778, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_372240_1255011, context_12_372241_1314660, context_12_372242_1314715, context_12_372243_1314777.", DescribeRole.Theorem),
            Node("context-11-93075-1316539", "context_11_93075_1316539", "Context at depth 11, code 93075, node 1316539",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93075 and original node 1316539, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_372300_1316459, context_12_372301_1316484, context_12_372302_1316509, context_12_372303_1316538.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
