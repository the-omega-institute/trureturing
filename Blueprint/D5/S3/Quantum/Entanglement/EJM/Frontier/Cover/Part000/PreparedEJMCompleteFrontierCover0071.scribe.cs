using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0071Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0071.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0071",
        H("Original frontier context coverage 0071"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03411", "selected_cut_03411", "Selected cut at depth 13, code 27753, node 107534",
                "At remaining fuel 8 and original index 107534, selection on the full partial prefix of depth 13 and code 27753 returns the complete row with depth 13, base-four code 27753, original node 107534, kind 2, reserved field 0, 2881 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03459", "selected_cut_03459", "Selected cut at depth 13, code 27822, node 108792",
                "At remaining fuel 8 and original index 108792, selection on the full partial prefix of depth 13 and code 27822 returns the complete row with depth 13, base-four code 27822, original node 108792, kind 2, reserved field 0, 2769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6938-107570", "unmarked_context_12_6938_107570", "Unmarked parent at depth 12, code 6938",
                "The frontier Boolean is false at remaining fuel 9, original node 107570, the whole prefixCache at depth 12 and code 6938, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-27821-108745", "unmarked_context_13_27821_108745", "Unmarked parent at depth 13, code 27821",
                "The frontier Boolean is false at remaining fuel 8, original node 108745, the whole prefixCache at depth 13 and code 27821, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6938-107570", "node_context_12_6938_107570", "Original split at fuel 9 and node 107570",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 107489, 107534, 107560, 107569. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-27821-108745", "node_context_13_27821_108745", "Original split at fuel 8 and node 108745",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 108672, 108703, 108725, 108744. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-27753-107534", "context_13_27753_107534", "Context at depth 13, code 27753, node 107534",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27753 and original node 107534, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-27822-108792", "context_13_27822_108792", "Context at depth 13, code 27822, node 108792",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27822 and original node 108792, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
