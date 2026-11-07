using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0938Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0938.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0938",
        H("Original frontier context coverage 0938"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45028", "selected_cut_45028", "Selected cut at depth 11, code 88912, node 1243268",
                "At remaining fuel 10 and original index 1243268, selection on the full partial prefix of depth 11 and code 88912 returns the complete row with depth 11, base-four code 88912, original node 1243268, kind 2, reserved field 0, 3397 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45075", "selected_cut_45075", "Selected cut at depth 12, code 355851, node 1244914",
                "At remaining fuel 9 and original index 1244914, selection on the full partial prefix of depth 12 and code 355851 returns the complete row with depth 12, base-four code 355851, original node 1244914, kind 2, reserved field 0, 3701 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22227-1243194", "unmarked_context_10_22227_1243194", "Unmarked parent at depth 10, code 22227",
                "The frontier Boolean is false at remaining fuel 11, original node 1243194, the whole prefixCache at depth 10 and code 22227, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88961-1244754", "unmarked_context_11_88961_1244754", "Unmarked parent at depth 11, code 88961",
                "The frontier Boolean is false at remaining fuel 10, original node 1244754, the whole prefixCache at depth 11 and code 88961, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22227-1243194", "node_context_10_22227_1243194", "Original split at fuel 11 and node 1243194",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1242980, 1243045, 1243193, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88961-1244754", "node_context_11_88961_1244754", "Original split at fuel 10 and node 1244754",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 1244675, 1244753. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-22227-1243194", "context_10_22227_1243194", "Context at depth 10, code 22227, node 1243194",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 22227 and original node 1243194, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_88908_1242980, context_11_88909_1243045, context_11_88910_1243193, context_11_88911_977886.", DescribeRole.Theorem),
            Node("context-12-355851-1244914", "context_12_355851_1244914", "Context at depth 12, code 355851, node 1244914",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355851 and original node 1244914, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
