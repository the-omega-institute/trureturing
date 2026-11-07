using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0347Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0347.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0347",
        H("Original frontier context coverage 0347"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16660", "selected_cut_16660", "Selected cut at depth 13, code 113710, node 423967",
                "At remaining fuel 8 and original index 423967, selection on the full partial prefix of depth 13 and code 113710 returns the complete row with depth 13, base-four code 113710, original node 423967, kind 2, reserved field 0, 2693 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16707", "selected_cut_16707", "Selected cut at depth 13, code 113751, node 425564",
                "At remaining fuel 8 and original index 425564, selection on the full partial prefix of depth 13 and code 113751 returns the complete row with depth 13, base-four code 113751, original node 425564, kind 2, reserved field 0, 713 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28427-423992", "unmarked_context_12_28427_423992", "Unmarked parent at depth 12, code 28427",
                "The frontier Boolean is false at remaining fuel 9, original node 423992, the whole prefixCache at depth 12 and code 28427, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28436-425454", "unmarked_context_12_28436_425454", "Unmarked parent at depth 12, code 28436",
                "The frontier Boolean is false at remaining fuel 9, original node 425454, the whole prefixCache at depth 12 and code 28436, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28427-423992", "node_context_12_28427_423992", "Original split at fuel 9 and node 423992",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 423834, 423933, 423967, 423991. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28436-425454", "node_context_12_28436_425454", "Original split at fuel 9 and node 425454",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 425381, 425420, 425448, 425453. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-113710-423967", "context_13_113710_423967", "Context at depth 13, code 113710, node 423967",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113710 and original node 423967, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-113751-425564", "context_13_113751_425564", "Context at depth 13, code 113751, node 425564",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 113751 and original node 425564, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
