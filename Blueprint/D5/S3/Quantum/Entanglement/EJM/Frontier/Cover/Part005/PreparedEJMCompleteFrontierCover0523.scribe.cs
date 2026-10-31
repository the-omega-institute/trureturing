using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0523Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0523.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0523",
        H("Original frontier context coverage 0523"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25109", "selected_cut_25109", "Selected cut at depth 13, code 310508, node 634681",
                "At remaining fuel 8 and original index 634681, selection on the full partial prefix of depth 13 and code 310508 returns the complete row with depth 13, base-four code 310508, original node 634681, kind 2, reserved field 0, 69 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25155", "selected_cut_25155", "Selected cut at depth 13, code 310572, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 310572 returns the complete row with depth 13, base-four code 310572, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77626-634677", "unmarked_context_12_77626_634677", "Unmarked parent at depth 12, code 77626",
                "The frontier Boolean is false at remaining fuel 9, original node 634677, the whole prefixCache at depth 12 and code 77626, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77642-635495", "unmarked_context_12_77642_635495", "Unmarked parent at depth 12, code 77642",
                "The frontier Boolean is false at remaining fuel 9, original node 635495, the whole prefixCache at depth 12 and code 77642, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77626-634677", "node_context_12_77626_634677", "Original split at fuel 9 and node 634677",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 634602, 634643, 634666, 634676. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77642-635495", "node_context_12_77642_635495", "Original split at fuel 9 and node 635495",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 635466, 635486, 635494. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77626-634677", "context_12_77626_634677", "Context at depth 12, code 77626, node 634677",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77626 and original node 634677, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_310504_634602, context_13_310505_634643, context_13_310506_634666, context_13_310507_634676.", DescribeRole.Theorem),
            Node("context-13-310572-3444", "context_13_310572_3444", "Context at depth 13, code 310572, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310572 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
