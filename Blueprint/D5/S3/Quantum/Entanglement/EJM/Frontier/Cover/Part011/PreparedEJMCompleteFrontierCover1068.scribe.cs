using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1068Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1068.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1068",
        H("Original frontier context coverage 1068"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51265", "selected_cut_51265", "Selected cut at depth 10, code 70144, node 1468246",
                "At remaining fuel 11 and original index 1468246, selection on the full partial prefix of depth 10 and code 70144 returns the complete row with depth 10, base-four code 70144, original node 1468246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51313", "selected_cut_51313", "Selected cut at depth 11, code 280711, node 1478763",
                "At remaining fuel 10 and original index 1478763, selection on the full partial prefix of depth 11 and code 280711 returns the complete row with depth 11, base-four code 280711, original node 1478763, kind 2, reserved field 0, 3249 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-70145-1476313", "unmarked_context_10_70145_1476313", "Unmarked parent at depth 10, code 70145",
                "The frontier Boolean is false at remaining fuel 11, original node 1476313, the whole prefixCache at depth 10 and code 70145, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-70177-1478764", "unmarked_context_10_70177_1478764", "Unmarked parent at depth 10, code 70177",
                "The frontier Boolean is false at remaining fuel 11, original node 1478764, the whole prefixCache at depth 10 and code 70177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-70145-1476313", "node_context_10_70145_1476313", "Original split at fuel 11 and node 1476313",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1476069, 1468419, 1476204, 1476312. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-70177-1478764", "node_context_10_70177_1478764", "Original split at fuel 11 and node 1478764",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1478561, 1468419, 1478664, 1478763. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-70144-1468246", "context_10_70144_1468246", "Context at depth 10, code 70144, node 1468246",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70144 and original node 1468246, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-70177-1478764", "context_10_70177_1478764", "Context at depth 10, code 70177, node 1478764",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 70177 and original node 1478764, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_280708_1478561, context_11_280709_1468419, context_11_280710_1478664, context_11_280711_1478763.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
