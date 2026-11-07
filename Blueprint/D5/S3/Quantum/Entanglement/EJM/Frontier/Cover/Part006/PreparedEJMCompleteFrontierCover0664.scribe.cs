using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0664Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0664.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0664",
        H("Original frontier context coverage 0664"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31876", "selected_cut_31876", "Selected cut at depth 13, code 430267, node 817866",
                "At remaining fuel 8 and original index 817866, selection on the full partial prefix of depth 13 and code 430267 returns the complete row with depth 13, base-four code 430267, original node 817866, kind 2, reserved field 0, 825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31922", "selected_cut_31922", "Selected cut at depth 12, code 107618, node 819797",
                "At remaining fuel 9 and original index 819797, selection on the full partial prefix of depth 12 and code 107618 returns the complete row with depth 12, base-four code 107618, original node 819797, kind 2, reserved field 0, 2497 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107566-817867", "unmarked_context_12_107566_817867", "Unmarked parent at depth 12, code 107566",
                "The frontier Boolean is false at remaining fuel 9, original node 817867, the whole prefixCache at depth 12 and code 107566, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6725-819661", "unmarked_context_10_6725_819661", "Unmarked parent at depth 10, code 6725",
                "The frontier Boolean is false at remaining fuel 11, original node 819661, the whole prefixCache at depth 10 and code 6725, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107566-817867", "node_context_12_107566_817867", "Original split at fuel 9 and node 817867",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 817796, 817845, 817859, 817866. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6725-819661", "node_context_10_6725_819661", "Original split at fuel 11 and node 819661",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 819210, 451541, 819426, 819660. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-430267-817866", "context_13_430267_817866", "Context at depth 13, code 430267, node 817866",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 430267 and original node 817866, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-107618-819797", "context_12_107618_819797", "Context at depth 12, code 107618, node 819797",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107618 and original node 819797, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
