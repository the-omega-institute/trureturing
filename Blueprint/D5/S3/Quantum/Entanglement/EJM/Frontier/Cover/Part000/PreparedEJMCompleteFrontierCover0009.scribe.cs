using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0009Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0009.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0009",
        H("Original frontier context coverage 0009"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00435", "selected_cut_00435", "Selected cut at depth 13, code 5484, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 5484 returns the complete row with depth 13, base-four code 5484, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00481", "selected_cut_00481", "Selected cut at depth 11, code 358, node 22610",
                "At remaining fuel 10 and original index 22610, selection on the full partial prefix of depth 11 and code 358 returns the complete row with depth 11, base-four code 358, original node 22610, kind 2, reserved field 0, 3653 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1370-20243", "unmarked_context_12_1370_20243", "Unmarked parent at depth 12, code 1370",
                "The frontier Boolean is false at remaining fuel 9, original node 20243, the whole prefixCache at depth 12 and code 1370, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-357-22469", "unmarked_context_11_357_22469", "Unmarked parent at depth 11, code 357",
                "The frontier Boolean is false at remaining fuel 10, original node 22469, the whole prefixCache at depth 11 and code 357, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1370-20243", "node_context_12_1370_20243", "Original split at fuel 9 and node 20243",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 20193, 20223, 20242. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-357-22469", "node_context_11_357_22469", "Original split at fuel 10 and node 22469",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 22218, 22343, 22468. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-1370-20243", "context_12_1370_20243", "Context at depth 12, code 1370, node 20243",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1370 and original node 20243, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_5480_3444, context_13_5481_20193, context_13_5482_20223, context_13_5483_20242.", DescribeRole.Theorem),
            Node("context-11-358-22610", "context_11_358_22610", "Context at depth 11, code 358, node 22610",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 358 and original node 22610, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
