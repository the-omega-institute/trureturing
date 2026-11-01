using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0724Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0724.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0724",
        H("Original frontier context coverage 0724"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34754", "selected_cut_34754", "Selected cut at depth 12, code 282635, node 907253",
                "At remaining fuel 9 and original index 907253, selection on the full partial prefix of depth 12 and code 282635 returns the complete row with depth 12, base-four code 282635, original node 907253, kind 2, reserved field 0, 2973 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34801", "selected_cut_34801", "Selected cut at depth 10, code 17674, node 908861",
                "At remaining fuel 11 and original index 908861, selection on the full partial prefix of depth 10 and code 17674 returns the complete row with depth 10, base-four code 17674, original node 908861, kind 2, reserved field 0, 2257 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70658-907254", "unmarked_context_11_70658_907254", "Unmarked parent at depth 11, code 70658",
                "The frontier Boolean is false at remaining fuel 10, original node 907254, the whole prefixCache at depth 11 and code 70658, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17673-908774", "unmarked_context_10_17673_908774", "Unmarked parent at depth 10, code 17673",
                "The frontier Boolean is false at remaining fuel 11, original node 908774, the whole prefixCache at depth 10 and code 17673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70658-907254", "node_context_11_70658_907254", "Original split at fuel 10 and node 907254",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 907055, 907123, 907186, 907253. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17673-908774", "node_context_10_17673_908774", "Original split at fuel 11 and node 908774",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 908615, 908663, 908727, 908773. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-282635-907253", "context_12_282635_907253", "Context at depth 12, code 282635, node 907253",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 282635 and original node 907253, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-17674-908861", "context_10_17674_908861", "Context at depth 10, code 17674, node 908861",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17674 and original node 908861, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
