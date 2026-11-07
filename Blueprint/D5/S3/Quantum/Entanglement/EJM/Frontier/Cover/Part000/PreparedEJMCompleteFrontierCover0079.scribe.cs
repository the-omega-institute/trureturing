using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0079Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0079.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0079",
        H("Original frontier context coverage 0079"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03794", "selected_cut_03794", "Selected cut at depth 13, code 69782, node 120550",
                "At remaining fuel 8 and original index 120550, selection on the full partial prefix of depth 13 and code 69782 returns the complete row with depth 13, base-four code 69782, original node 120550, kind 2, reserved field 0, 1397 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03841", "selected_cut_03841", "Selected cut at depth 13, code 70666, node 123332",
                "At remaining fuel 8 and original index 123332, selection on the full partial prefix of depth 13 and code 70666 returns the complete row with depth 13, base-four code 70666, original node 123332, kind 2, reserved field 0, 2161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17445-120568", "unmarked_context_12_17445_120568", "Unmarked parent at depth 12, code 17445",
                "The frontier Boolean is false at remaining fuel 9, original node 120568, the whole prefixCache at depth 12 and code 17445, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-70664-123240", "unmarked_context_13_70664_123240", "Unmarked parent at depth 13, code 70664",
                "The frontier Boolean is false at remaining fuel 8, original node 123240, the whole prefixCache at depth 13 and code 70664, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17445-120568", "node_context_12_17445_120568", "Original split at fuel 9 and node 120568",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 120471, 120522, 120550, 120567. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-70664-123240", "node_context_13_70664_123240", "Original split at fuel 8 and node 123240",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 123182, 123198, 123220, 123239. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-69782-120550", "context_13_69782_120550", "Context at depth 13, code 69782, node 120550",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 69782 and original node 120550, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-70666-123332", "context_13_70666_123332", "Context at depth 13, code 70666, node 123332",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 70666 and original node 123332, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
