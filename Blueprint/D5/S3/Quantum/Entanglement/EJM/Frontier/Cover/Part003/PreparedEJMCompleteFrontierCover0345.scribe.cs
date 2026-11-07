using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0345Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0345.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0345",
        H("Original frontier context coverage 0345"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16564", "selected_cut_16564", "Selected cut at depth 12, code 28324, node 421346",
                "At remaining fuel 9 and original index 421346, selection on the full partial prefix of depth 12 and code 28324 returns the complete row with depth 12, base-four code 28324, original node 421346, kind 2, reserved field 0, 1401 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16611", "selected_cut_16611", "Selected cut at depth 14, code 454755, node 422465",
                "At remaining fuel 7 and original index 422465, selection on the full partial prefix of depth 14 and code 454755 returns the complete row with depth 14, base-four code 454755, original node 422465, kind 2, reserved field 0, 1113 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7080-421331", "unmarked_context_11_7080_421331", "Unmarked parent at depth 11, code 7080",
                "The frontier Boolean is false at remaining fuel 10, original node 421331, the whole prefixCache at depth 11 and code 7080, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28421-422349", "unmarked_context_12_28421_422349", "Unmarked parent at depth 12, code 28421",
                "The frontier Boolean is false at remaining fuel 9, original node 422349, the whole prefixCache at depth 12 and code 28421, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7080-421331", "node_context_11_7080_421331", "Original split at fuel 10 and node 421331",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 421267, 421288, 421308, 421330. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28421-422349", "node_context_12_28421_422349", "Original split at fuel 9 and node 422349",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 422129, 422268, 422336, 422348. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-7080-421331", "context_11_7080_421331", "Context at depth 11, code 7080, node 421331",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7080 and original node 421331, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28320_421267, context_12_28321_421288, context_12_28322_421308, context_12_28323_421330.", DescribeRole.Theorem),
            Node("context-14-454755-422465", "context_14_454755_422465", "Context at depth 14, code 454755, node 422465",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 454755 and original node 422465, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
