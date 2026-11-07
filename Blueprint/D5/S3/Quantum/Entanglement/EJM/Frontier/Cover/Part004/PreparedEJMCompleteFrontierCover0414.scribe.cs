using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0414Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0414.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0414",
        H("Original frontier context coverage 0414"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19875", "selected_cut_19875", "Selected cut at depth 13, code 289872, node 508825",
                "At remaining fuel 8 and original index 508825, selection on the full partial prefix of depth 13 and code 289872 returns the complete row with depth 13, base-four code 289872, original node 508825, kind 2, reserved field 0, 1273 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19922", "selected_cut_19922", "Selected cut at depth 13, code 289919, node 510228",
                "At remaining fuel 8 and original index 510228, selection on the full partial prefix of depth 13 and code 289919 returns the complete row with depth 13, base-four code 289919, original node 510228, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18116-508769", "unmarked_context_11_18116_508769", "Unmarked parent at depth 11, code 18116",
                "The frontier Boolean is false at remaining fuel 10, original node 508769, the whole prefixCache at depth 11 and code 18116, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18119-510230", "unmarked_context_11_18119_510230", "Unmarked parent at depth 11, code 18119",
                "The frontier Boolean is false at remaining fuel 10, original node 510230, the whole prefixCache at depth 11 and code 18119, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18116-508769", "node_context_11_18116_508769", "Original split at fuel 10 and node 508769",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 508547, 508669, 508768. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18119-510230", "node_context_11_18119_510230", "Original split at fuel 10 and node 510230",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 509856, 509938, 510033, 510229. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18116-508769", "context_11_18116_508769", "Context at depth 11, code 18116, node 508769",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18116 and original node 508769, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_72464_435160, context_12_72465_508547, context_12_72466_508669, context_12_72467_508768.", DescribeRole.Theorem),
            Node("context-11-18119-510230", "context_11_18119_510230", "Context at depth 11, code 18119, node 510230",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18119 and original node 510230, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_72476_509856, context_12_72477_509938, context_12_72478_510033, context_12_72479_510229.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
