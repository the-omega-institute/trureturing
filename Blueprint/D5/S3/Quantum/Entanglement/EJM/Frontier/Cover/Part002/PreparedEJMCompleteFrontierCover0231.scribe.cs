using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0231Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0231.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0231",
        H("Original frontier context coverage 0231"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11091", "selected_cut_11091", "Selected cut at depth 12, code 25422, node 297560",
                "At remaining fuel 9 and original index 297560, selection on the full partial prefix of depth 12 and code 25422 returns the complete row with depth 12, base-four code 25422, original node 297560, kind 2, reserved field 0, 3665 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11138", "selected_cut_11138", "Selected cut at depth 13, code 101783, node 298688",
                "At remaining fuel 8 and original index 298688, selection on the full partial prefix of depth 13 and code 101783 returns the complete row with depth 13, base-four code 101783, original node 298688, kind 2, reserved field 0, 937 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25423-297659", "unmarked_context_12_25423_297659", "Unmarked parent at depth 12, code 25423",
                "The frontier Boolean is false at remaining fuel 9, original node 297659, the whole prefixCache at depth 12 and code 25423, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25445-298689", "unmarked_context_12_25445_298689", "Unmarked parent at depth 12, code 25445",
                "The frontier Boolean is false at remaining fuel 9, original node 298689, the whole prefixCache at depth 12 and code 25445, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25423-297659", "node_context_12_25423_297659", "Original split at fuel 9 and node 297659",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 297597, 297629, 297658. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25445-298689", "node_context_12_25445_298689", "Original split at fuel 9 and node 298689",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 298642, 298677, 298688. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25422-297560", "context_12_25422_297560", "Context at depth 12, code 25422, node 297560",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25422 and original node 297560, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25445-298689", "context_12_25445_298689", "Context at depth 12, code 25445, node 298689",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25445 and original node 298689, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_101780_3444, context_13_101781_298642, context_13_101782_298677, context_13_101783_298688.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
