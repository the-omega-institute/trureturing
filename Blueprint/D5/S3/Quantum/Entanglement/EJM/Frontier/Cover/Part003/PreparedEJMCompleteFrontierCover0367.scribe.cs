using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0367Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0367.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0367",
        H("Original frontier context coverage 0367"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17618", "selected_cut_17618", "Selected cut at depth 13, code 282665, node 449224",
                "At remaining fuel 8 and original index 449224, selection on the full partial prefix of depth 13 and code 282665 returns the complete row with depth 13, base-four code 282665, original node 449224, kind 2, reserved field 0, 2349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17665", "selected_cut_17665", "Selected cut at depth 13, code 282763, node 450123",
                "At remaining fuel 8 and original index 450123, selection on the full partial prefix of depth 13 and code 282763 returns the complete row with depth 13, base-four code 282763, original node 450123, kind 2, reserved field 0, 709 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70666-449257", "unmarked_context_12_70666_449257", "Unmarked parent at depth 12, code 70666",
                "The frontier Boolean is false at remaining fuel 9, original node 449257, the whole prefixCache at depth 12 and code 70666, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-70690-450124", "unmarked_context_12_70690_450124", "Unmarked parent at depth 12, code 70690",
                "The frontier Boolean is false at remaining fuel 9, original node 450124, the whole prefixCache at depth 12 and code 70690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70666-449257", "node_context_12_70666_449257", "Original split at fuel 9 and node 449257",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 449189, 449224, 449246, 449256. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-70690-450124", "node_context_12_70690_450124", "Original split at fuel 9 and node 450124",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 450070, 450097, 450117, 450123. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-282665-449224", "context_13_282665_449224", "Context at depth 13, code 282665, node 449224",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 282665 and original node 449224, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-70690-450124", "context_12_70690_450124", "Context at depth 12, code 70690, node 450124",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70690 and original node 450124, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_282760_450070, context_13_282761_450097, context_13_282762_450117, context_13_282763_450123.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
