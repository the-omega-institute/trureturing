using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0592Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0592.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0592",
        H("Original frontier context coverage 0592"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28420", "selected_cut_28420", "Selected cut at depth 13, code 369787, node 717896",
                "At remaining fuel 8 and original index 717896, selection on the full partial prefix of depth 13 and code 369787 returns the complete row with depth 13, base-four code 369787, original node 717896, kind 2, reserved field 0, 901 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28467", "selected_cut_28467", "Selected cut at depth 13, code 369846, node 718703",
                "At remaining fuel 8 and original index 718703, selection on the full partial prefix of depth 13 and code 369846 returns the complete row with depth 13, base-four code 369846, original node 718703, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92446-717897", "unmarked_context_12_92446_717897", "Unmarked parent at depth 12, code 92446",
                "The frontier Boolean is false at remaining fuel 9, original node 717897, the whole prefixCache at depth 12 and code 92446, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92460-718656", "unmarked_context_12_92460_718656", "Unmarked parent at depth 12, code 92460",
                "The frontier Boolean is false at remaining fuel 9, original node 718656, the whole prefixCache at depth 12 and code 92460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92446-717897", "node_context_12_92446_717897", "Original split at fuel 9 and node 717897",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 717848, 717868, 717888, 717896. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92460-718656", "node_context_12_92460_718656", "Original split at fuel 9 and node 718656",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 718604, 718626, 718645, 718655. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-369787-717896", "context_13_369787_717896", "Context at depth 13, code 369787, node 717896",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369787 and original node 717896, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-369846-718703", "context_13_369846_718703", "Context at depth 13, code 369846, node 718703",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369846 and original node 718703, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
