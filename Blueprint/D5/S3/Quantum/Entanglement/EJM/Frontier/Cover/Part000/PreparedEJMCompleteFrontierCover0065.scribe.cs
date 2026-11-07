using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0065Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0065.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0065",
        H("Original frontier context coverage 0065"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03123", "selected_cut_03123", "Selected cut at depth 13, code 26937, node 97056",
                "At remaining fuel 8 and original index 97056, selection on the full partial prefix of depth 13 and code 26937 returns the complete row with depth 13, base-four code 26937, original node 97056, kind 2, reserved field 0, 2773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03169", "selected_cut_03169", "Selected cut at depth 13, code 27007, node 98787",
                "At remaining fuel 8 and original index 98787, selection on the full partial prefix of depth 13 and code 27007 returns the complete row with depth 13, base-four code 27007, original node 98787, kind 2, reserved field 0, 1481 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6734-97152", "unmarked_context_12_6734_97152", "Unmarked parent at depth 12, code 6734",
                "The frontier Boolean is false at remaining fuel 9, original node 97152, the whole prefixCache at depth 12 and code 6734, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-421-98790", "unmarked_context_10_421_98790", "Unmarked parent at depth 10, code 421",
                "The frontier Boolean is false at remaining fuel 11, original node 98790, the whole prefixCache at depth 10 and code 421, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6734-97152", "node_context_12_6734_97152", "Original split at fuel 9 and node 97152",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 97056, 97114, 97151. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-421-98790", "node_context_10_421_98790", "Original split at fuel 11 and node 98790",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 97643, 97985, 98428, 98789. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-26937-97056", "context_13_26937_97056", "Context at depth 13, code 26937, node 97056",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 26937 and original node 97056, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-421-98790", "context_10_421_98790", "Context at depth 10, code 421, node 98790",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 421 and original node 98790, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_1684_97643, context_11_1685_97985, context_11_1686_98428, context_11_1687_98789.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
