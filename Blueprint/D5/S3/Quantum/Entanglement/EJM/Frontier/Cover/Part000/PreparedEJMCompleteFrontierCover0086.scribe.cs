using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0086Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0086.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0086",
        H("Original frontier context coverage 0086"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04130", "selected_cut_04130", "Selected cut at depth 13, code 71825, node 131056",
                "At remaining fuel 8 and original index 131056, selection on the full partial prefix of depth 13 and code 71825 returns the complete row with depth 13, base-four code 71825, original node 131056, kind 2, reserved field 0, 1765 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04178", "selected_cut_04178", "Selected cut at depth 13, code 71879, node 132092",
                "At remaining fuel 8 and original index 132092, selection on the full partial prefix of depth 13 and code 71879 returns the complete row with depth 13, base-four code 71879, original node 132092, kind 2, reserved field 0, 725 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-17956-131091", "unmarked_context_12_17956_131091", "Unmarked parent at depth 12, code 17956",
                "The frontier Boolean is false at remaining fuel 9, original node 131091, the whole prefixCache at depth 12 and code 17956, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-17968-131990", "unmarked_context_12_17968_131990", "Unmarked parent at depth 12, code 17968",
                "The frontier Boolean is false at remaining fuel 9, original node 131990, the whole prefixCache at depth 12 and code 17968, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-17956-131091", "node_context_12_17956_131091", "Original split at fuel 9 and node 131091",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 131035, 131056, 131077, 131090. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-17968-131990", "node_context_12_17968_131990", "Original split at fuel 9 and node 131990",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 131898, 131960, 131978, 131989. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-71825-131056", "context_13_71825_131056", "Context at depth 13, code 71825, node 131056",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71825 and original node 131056, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-71879-132092", "context_13_71879_132092", "Context at depth 13, code 71879, node 132092",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 71879 and original node 132092, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
