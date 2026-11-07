using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0248Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0248.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0248",
        H("Original frontier context coverage 0248"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11907", "selected_cut_11907", "Selected cut at depth 13, code 103596, node 318045",
                "At remaining fuel 8 and original index 318045, selection on the full partial prefix of depth 13 and code 103596 returns the complete row with depth 13, base-four code 103596, original node 318045, kind 2, reserved field 0, 1217 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11954", "selected_cut_11954", "Selected cut at depth 13, code 103643, node 318916",
                "At remaining fuel 8 and original index 318916, selection on the full partial prefix of depth 13 and code 103643 returns the complete row with depth 13, base-four code 103643, original node 318916, kind 2, reserved field 0, 981 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25899-318105", "unmarked_context_12_25899_318105", "Unmarked parent at depth 12, code 25899",
                "The frontier Boolean is false at remaining fuel 9, original node 318105, the whole prefixCache at depth 12 and code 25899, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25910-318917", "unmarked_context_12_25910_318917", "Unmarked parent at depth 12, code 25910",
                "The frontier Boolean is false at remaining fuel 9, original node 318917, the whole prefixCache at depth 12 and code 25910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25899-318105", "node_context_12_25899_318105", "Original split at fuel 9 and node 318105",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 318045, 318076, 318097, 318104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25910-318917", "node_context_12_25910_318917", "Original split at fuel 9 and node 318917",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 318865, 318890, 318906, 318916. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-103596-318045", "context_13_103596_318045", "Context at depth 13, code 103596, node 318045",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103596 and original node 318045, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25910-318917", "context_12_25910_318917", "Context at depth 12, code 25910, node 318917",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25910 and original node 318917, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103640_318865, context_13_103641_318890, context_13_103642_318906, context_13_103643_318916.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
