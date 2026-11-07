using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0268Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0268.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0268",
        H("Original frontier context coverage 0268"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12867", "selected_cut_12867", "Selected cut at depth 13, code 105633, node 339266",
                "At remaining fuel 8 and original index 339266, selection on the full partial prefix of depth 13 and code 105633 returns the complete row with depth 13, base-four code 105633, original node 339266, kind 2, reserved field 0, 2005 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12914", "selected_cut_12914", "Selected cut at depth 13, code 105683, node 340202",
                "At remaining fuel 8 and original index 340202, selection on the full partial prefix of depth 13 and code 105683 returns the complete row with depth 13, base-four code 105683, original node 340202, kind 2, reserved field 0, 789 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26408-339295", "unmarked_context_12_26408_339295", "Unmarked parent at depth 12, code 26408",
                "The frontier Boolean is false at remaining fuel 9, original node 339295, the whole prefixCache at depth 12 and code 26408, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26420-340203", "unmarked_context_12_26420_340203", "Unmarked parent at depth 12, code 26420",
                "The frontier Boolean is false at remaining fuel 9, original node 340203, the whole prefixCache at depth 12 and code 26420, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26408-339295", "node_context_12_26408_339295", "Original split at fuel 9 and node 339295",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 339237, 339266, 339284, 339294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26420-340203", "node_context_12_26420_340203", "Original split at fuel 9 and node 340203",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 340146, 340182, 340197, 340202. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105633-339266", "context_13_105633_339266", "Context at depth 13, code 105633, node 339266",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105633 and original node 339266, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-26420-340203", "context_12_26420_340203", "Context at depth 12, code 26420, node 340203",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26420 and original node 340203, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_105680_340146, context_13_105681_340182, context_13_105682_340197, context_13_105683_340202.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
