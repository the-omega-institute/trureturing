using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0237Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0237.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0237",
        H("Original frontier context coverage 0237"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11378", "selected_cut_11378", "Selected cut at depth 13, code 102533, node 305189",
                "At remaining fuel 8 and original index 305189, selection on the full partial prefix of depth 13 and code 102533 returns the complete row with depth 13, base-four code 102533, original node 305189, kind 2, reserved field 0, 1621 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11426", "selected_cut_11426", "Selected cut at depth 13, code 102587, node 306019",
                "At remaining fuel 8 and original index 306019, selection on the full partial prefix of depth 13 and code 102587 returns the complete row with depth 13, base-four code 102587, original node 306019, kind 2, reserved field 0, 805 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25633-305213", "unmarked_context_12_25633_305213", "Unmarked parent at depth 12, code 25633",
                "The frontier Boolean is false at remaining fuel 9, original node 305213, the whole prefixCache at depth 12 and code 25633, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25646-306020", "unmarked_context_12_25646_306020", "Unmarked parent at depth 12, code 25646",
                "The frontier Boolean is false at remaining fuel 9, original node 306020, the whole prefixCache at depth 12 and code 25646, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25633-305213", "node_context_12_25633_305213", "Original split at fuel 9 and node 305213",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 305163, 305189, 305204, 305212. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25646-306020", "node_context_12_25646_306020", "Original split at fuel 9 and node 306020",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 305969, 305996, 306008, 306019. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102533-305189", "context_13_102533_305189", "Context at depth 13, code 102533, node 305189",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102533 and original node 305189, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25646-306020", "context_12_25646_306020", "Context at depth 12, code 25646, node 306020",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25646 and original node 306020, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_102584_305969, context_13_102585_305996, context_13_102586_306008, context_13_102587_306019.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
