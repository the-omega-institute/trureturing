using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0207Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0207.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0207",
        H("Original frontier context coverage 0207"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09937", "selected_cut_09937", "Selected cut at depth 11, code 6208, node 167448",
                "At remaining fuel 10 and original index 167448, selection on the full partial prefix of depth 11 and code 6208 returns the complete row with depth 11, base-four code 6208, original node 167448, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09986", "selected_cut_09986", "Selected cut at depth 13, code 99386, node 274555",
                "At remaining fuel 8 and original index 274555, selection on the full partial prefix of depth 13 and code 99386 returns the complete row with depth 13, base-four code 99386, original node 274555, kind 2, reserved field 0, 2333 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-99348-273241", "unmarked_context_13_99348_273241", "Unmarked parent at depth 13, code 99348",
                "The frontier Boolean is false at remaining fuel 8, original node 273241, the whole prefixCache at depth 13 and code 99348, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24845-274443", "unmarked_context_12_24845_274443", "Unmarked parent at depth 12, code 24845",
                "The frontier Boolean is false at remaining fuel 9, original node 274443, the whole prefixCache at depth 12 and code 24845, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-99348-273241", "node_context_13_99348_273241", "Original split at fuel 8 and node 273241",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 273183, 273196, 273216, 273240. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24845-274443", "node_context_12_24845_274443", "Original split at fuel 9 and node 274443",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 274368, 274405, 274432, 274442. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6208-167448", "context_11_6208_167448", "Context at depth 11, code 6208, node 167448",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6208 and original node 167448, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99386-274555", "context_13_99386_274555", "Context at depth 13, code 99386, node 274555",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99386 and original node 274555, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
