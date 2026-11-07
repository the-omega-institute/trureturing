using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0029Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0029.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0029",
        H("Original frontier context coverage 0029"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01394", "selected_cut_01394", "Selected cut at depth 13, code 18485, node 51248",
                "At remaining fuel 8 and original index 51248, selection on the full partial prefix of depth 13 and code 18485 returns the complete row with depth 13, base-four code 18485, original node 51248, kind 2, reserved field 0, 3873 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01441", "selected_cut_01441", "Selected cut at depth 13, code 18532, node 52635",
                "At remaining fuel 8 and original index 52635, selection on the full partial prefix of depth 13 and code 18532 returns the complete row with depth 13, base-four code 18532, original node 52635, kind 2, reserved field 0, 2049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4621-51295", "unmarked_context_12_4621_51295", "Unmarked parent at depth 12, code 4621",
                "The frontier Boolean is false at remaining fuel 9, original node 51295, the whole prefixCache at depth 12 and code 4621, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4632-52592", "unmarked_context_12_4632_52592", "Unmarked parent at depth 12, code 4632",
                "The frontier Boolean is false at remaining fuel 9, original node 52592, the whole prefixCache at depth 12 and code 4632, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4621-51295", "node_context_12_4621_51295", "Original split at fuel 9 and node 51295",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 51198, 51248, 51285, 51294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4632-52592", "node_context_12_4632_52592", "Original split at fuel 9 and node 52592",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 52494, 52543, 52575, 52591. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18485-51248", "context_13_18485_51248", "Context at depth 13, code 18485, node 51248",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18485 and original node 51248, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-18532-52635", "context_13_18532_52635", "Context at depth 13, code 18532, node 52635",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18532 and original node 52635, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
