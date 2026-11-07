using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0659Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0659.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0659",
        H("Original frontier context coverage 0659"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31636", "selected_cut_31636", "Selected cut at depth 13, code 424270, node 811263",
                "At remaining fuel 8 and original index 811263, selection on the full partial prefix of depth 13 and code 424270 returns the complete row with depth 13, base-four code 424270, original node 811263, kind 2, reserved field 0, 1721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31683", "selected_cut_31683", "Selected cut at depth 12, code 106098, node 812807",
                "At remaining fuel 9 and original index 812807, selection on the full partial prefix of depth 12 and code 106098 returns the complete row with depth 12, base-four code 106098, original node 812807, kind 2, reserved field 0, 2561 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106067-811278", "unmarked_context_12_106067_811278", "Unmarked parent at depth 12, code 106067",
                "The frontier Boolean is false at remaining fuel 9, original node 811278, the whole prefixCache at depth 12 and code 106067, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6630-812673", "unmarked_context_10_6630_812673", "Unmarked parent at depth 10, code 6630",
                "The frontier Boolean is false at remaining fuel 11, original node 812673, the whole prefixCache at depth 10 and code 6630, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106067-811278", "node_context_12_106067_811278", "Original split at fuel 9 and node 811278",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 811231, 811263, 811277. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6630-812673", "node_context_10_6630_812673", "Original split at fuel 11 and node 812673",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 812158, 812358, 812505, 812672. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424270-811263", "context_13_424270_811263", "Context at depth 13, code 424270, node 811263",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424270 and original node 811263, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-106098-812807", "context_12_106098_812807", "Context at depth 12, code 106098, node 812807",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 106098 and original node 812807, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
