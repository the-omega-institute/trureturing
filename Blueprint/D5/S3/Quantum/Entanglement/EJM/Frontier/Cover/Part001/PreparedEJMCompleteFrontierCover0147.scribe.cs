using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0147Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0147.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0147",
        H("Original frontier context coverage 0147"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07060", "selected_cut_07060", "Selected cut at depth 13, code 88300, node 207065",
                "At remaining fuel 8 and original index 207065, selection on the full partial prefix of depth 13 and code 88300 returns the complete row with depth 13, base-four code 88300, original node 207065, kind 2, reserved field 0, 233 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07106", "selected_cut_07106", "Selected cut at depth 13, code 88346, node 207920",
                "At remaining fuel 8 and original index 207920, selection on the full partial prefix of depth 13 and code 88346 returns the complete row with depth 13, base-four code 88346, original node 207920, kind 2, reserved field 0, 1385 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22074-207059", "unmarked_context_12_22074_207059", "Unmarked parent at depth 12, code 22074",
                "The frontier Boolean is false at remaining fuel 9, original node 207059, the whole prefixCache at depth 12 and code 22074, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22085-207865", "unmarked_context_12_22085_207865", "Unmarked parent at depth 12, code 22085",
                "The frontier Boolean is false at remaining fuel 9, original node 207865, the whole prefixCache at depth 12 and code 22085, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22074-207059", "node_context_12_22074_207059", "Original split at fuel 9 and node 207059",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 206948, 207025, 207045, 207058. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22085-207865", "node_context_12_22085_207865", "Original split at fuel 9 and node 207865",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 207825, 207848, 207864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22074-207059", "context_12_22074_207059", "Context at depth 12, code 22074, node 207059",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22074 and original node 207059, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_88296_206948, context_13_88297_207025, context_13_88298_207045, context_13_88299_207058.", DescribeRole.Theorem),
            Node("context-13-88346-207920", "context_13_88346_207920", "Context at depth 13, code 88346, node 207920",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88346 and original node 207920, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
