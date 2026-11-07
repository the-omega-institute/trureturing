using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0377Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0377.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0377",
        H("Original frontier context coverage 0377"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18099", "selected_cut_18099", "Selected cut at depth 13, code 284811, node 464236",
                "At remaining fuel 8 and original index 464236, selection on the full partial prefix of depth 13 and code 284811 returns the complete row with depth 13, base-four code 284811, original node 464236, kind 2, reserved field 0, 721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18145", "selected_cut_18145", "Selected cut at depth 13, code 284863, node 465194",
                "At remaining fuel 8 and original index 465194, selection on the full partial prefix of depth 13 and code 284863 returns the complete row with depth 13, base-four code 284863, original node 465194, kind 2, reserved field 0, 741 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71202-464237", "unmarked_context_12_71202_464237", "Unmarked parent at depth 12, code 71202",
                "The frontier Boolean is false at remaining fuel 9, original node 464237, the whole prefixCache at depth 12 and code 71202, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4450-465197", "unmarked_context_10_4450_465197", "Unmarked parent at depth 10, code 4450",
                "The frontier Boolean is false at remaining fuel 11, original node 465197, the whole prefixCache at depth 10 and code 4450, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71202-464237", "node_context_12_71202_464237", "Original split at fuel 9 and node 464237",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 464189, 464214, 464232, 464236. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4450-465197", "node_context_10_4450_465197", "Original split at fuel 11 and node 465197",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 464316, 464652, 464856, 465196. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-284811-464236", "context_13_284811_464236", "Context at depth 13, code 284811, node 464236",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 284811 and original node 464236, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-4450-465197", "context_10_4450_465197", "Context at depth 10, code 4450, node 465197",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4450 and original node 465197, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_17800_464316, context_11_17801_464652, context_11_17802_464856, context_11_17803_465196.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
