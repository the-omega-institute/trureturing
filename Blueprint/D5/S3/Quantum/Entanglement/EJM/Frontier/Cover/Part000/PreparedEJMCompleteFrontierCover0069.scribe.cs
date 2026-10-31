using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0069Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0069.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0069",
        H("Original frontier context coverage 0069"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03315", "selected_cut_03315", "Selected cut at depth 14, code 110694, node 104608",
                "At remaining fuel 7 and original index 104608, selection on the full partial prefix of depth 14 and code 110694 returns the complete row with depth 14, base-four code 110694, original node 104608, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03363", "selected_cut_03363", "Selected cut at depth 14, code 110823, node 106038",
                "At remaining fuel 7 and original index 106038, selection on the full partial prefix of depth 14 and code 110823 returns the complete row with depth 14, base-four code 110823, original node 106038, kind 2, reserved field 0, 1033 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-27673-104630", "unmarked_context_13_27673_104630", "Unmarked parent at depth 13, code 27673",
                "The frontier Boolean is false at remaining fuel 8, original node 104630, the whole prefixCache at depth 13 and code 27673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-6925-105885", "unmarked_context_12_6925_105885", "Unmarked parent at depth 12, code 6925",
                "The frontier Boolean is false at remaining fuel 9, original node 105885, the whole prefixCache at depth 12 and code 6925, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-27673-104630", "node_context_13_27673_104630", "Original split at fuel 8 and node 104630",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 104565, 104585, 104608, 104629. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-6925-105885", "node_context_12_6925_105885", "Original split at fuel 9 and node 105885",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 105733, 105812, 105870, 105884. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-110694-104608", "context_14_110694_104608", "Context at depth 14, code 110694, node 104608",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 110694 and original node 104608, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-110823-106038", "context_14_110823_106038", "Context at depth 14, code 110823, node 106038",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 110823 and original node 106038, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
