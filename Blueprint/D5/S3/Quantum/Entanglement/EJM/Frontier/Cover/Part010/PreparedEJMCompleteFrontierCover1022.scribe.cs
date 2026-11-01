using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1022Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1022.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1022",
        H("Original frontier context coverage 1022"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49059", "selected_cut_49059", "Selected cut at depth 11, code 101388, node 1384871",
                "At remaining fuel 10 and original index 1384871, selection on the full partial prefix of depth 11 and code 101388 returns the complete row with depth 11, base-four code 101388, original node 1384871, kind 2, reserved field 0, 3357 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49106", "selected_cut_49106", "Selected cut at depth 11, code 101471, node 1386850",
                "At remaining fuel 10 and original index 1386850, selection on the full partial prefix of depth 11 and code 101471 returns the complete row with depth 11, base-four code 101471, original node 1386850, kind 2, reserved field 0, 453 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25346-1384765", "unmarked_context_10_25346_1384765", "Unmarked parent at depth 10, code 25346",
                "The frontier Boolean is false at remaining fuel 11, original node 1384765, the whole prefixCache at depth 10 and code 25346, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25367-1386851", "unmarked_context_10_25367_1386851", "Unmarked parent at depth 10, code 25367",
                "The frontier Boolean is false at remaining fuel 11, original node 1386851, the whole prefixCache at depth 10 and code 25367, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25346-1384765", "node_context_10_25346_1384765", "Original split at fuel 11 and node 1384765",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1384641, 1384702, 479708, 1384764. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25367-1386851", "node_context_10_25367_1386851", "Original split at fuel 11 and node 1386851",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1386733, 1386791, 1386836, 1386850. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-25346-1384765", "context_10_25346_1384765", "Context at depth 10, code 25346, node 1384765",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25346 and original node 1384765, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_101384_1384641, context_11_101385_1384702, context_11_101386_479708, context_11_101387_1384764.", DescribeRole.Theorem),
            Node("context-10-25367-1386851", "context_10_25367_1386851", "Context at depth 10, code 25367, node 1386851",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25367 and original node 1386851, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_101468_1386733, context_11_101469_1386791, context_11_101470_1386836, context_11_101471_1386850.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
