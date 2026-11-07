using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0506Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0506.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0506",
        H("Original frontier context coverage 0506"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24292", "selected_cut_24292", "Selected cut at depth 13, code 308350, node 614429",
                "At remaining fuel 8 and original index 614429, selection on the full partial prefix of depth 13 and code 308350 returns the complete row with depth 13, base-four code 308350, original node 614429, kind 2, reserved field 0, 1769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24339", "selected_cut_24339", "Selected cut at depth 13, code 308406, node 615494",
                "At remaining fuel 8 and original index 615494, selection on the full partial prefix of depth 13 and code 308406 returns the complete row with depth 13, base-four code 308406, original node 615494, kind 2, reserved field 0, 1717 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77087-614436", "unmarked_context_12_77087_614436", "Unmarked parent at depth 12, code 77087",
                "The frontier Boolean is false at remaining fuel 9, original node 614436, the whole prefixCache at depth 12 and code 77087, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77100-615435", "unmarked_context_12_77100_615435", "Unmarked parent at depth 12, code 77100",
                "The frontier Boolean is false at remaining fuel 9, original node 615435, the whole prefixCache at depth 12 and code 77100, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77087-614436", "node_context_12_77087_614436", "Original split at fuel 9 and node 614436",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 614377, 614405, 614429, 614435. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77100-615435", "node_context_12_77100_615435", "Original split at fuel 9 and node 615435",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 615355, 615388, 615425, 615434. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-308350-614429", "context_13_308350_614429", "Context at depth 13, code 308350, node 614429",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308350 and original node 614429, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-308406-615494", "context_13_308406_615494", "Context at depth 13, code 308406, node 615494",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308406 and original node 615494, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
