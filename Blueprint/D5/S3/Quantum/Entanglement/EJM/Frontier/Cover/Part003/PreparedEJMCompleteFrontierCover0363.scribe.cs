using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0363Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0363.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0363",
        H("Original frontier context coverage 0363"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17426", "selected_cut_17426", "Selected cut at depth 13, code 280661, node 443650",
                "At remaining fuel 8 and original index 443650, selection on the full partial prefix of depth 13 and code 280661 returns the complete row with depth 13, base-four code 280661, original node 443650, kind 2, reserved field 0, 1457 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17473", "selected_cut_17473", "Selected cut at depth 13, code 280711, node 444643",
                "At remaining fuel 8 and original index 444643, selection on the full partial prefix of depth 13 and code 280711 returns the complete row with depth 13, base-four code 280711, original node 444643, kind 2, reserved field 0, 809 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70165-443673", "unmarked_context_12_70165_443673", "Unmarked parent at depth 12, code 70165",
                "The frontier Boolean is false at remaining fuel 9, original node 443673, the whole prefixCache at depth 12 and code 70165, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-70177-444644", "unmarked_context_12_70177_444644", "Unmarked parent at depth 12, code 70177",
                "The frontier Boolean is false at remaining fuel 9, original node 444644, the whole prefixCache at depth 12 and code 70177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70165-443673", "node_context_12_70165_443673", "Original split at fuel 9 and node 443673",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 443629, 443650, 443667, 443672. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-70177-444644", "node_context_12_70177_444644", "Original split at fuel 9 and node 444644",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 444601, 444616, 444635, 444643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-280661-443650", "context_13_280661_443650", "Context at depth 13, code 280661, node 443650",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 280661 and original node 443650, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-70177-444644", "context_12_70177_444644", "Context at depth 12, code 70177, node 444644",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70177 and original node 444644, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_280708_444601, context_13_280709_444616, context_13_280710_444635, context_13_280711_444643.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
