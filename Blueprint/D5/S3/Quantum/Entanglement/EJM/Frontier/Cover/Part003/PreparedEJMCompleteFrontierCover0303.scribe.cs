using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0303Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0303.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0303",
        H("Original frontier context coverage 0303"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14548", "selected_cut_14548", "Selected cut at depth 12, code 27262, node 375259",
                "At remaining fuel 9 and original index 375259, selection on the full partial prefix of depth 12 and code 27262 returns the complete row with depth 12, base-four code 27262, original node 375259, kind 2, reserved field 0, 2301 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14594", "selected_cut_14594", "Selected cut at depth 12, code 27311, node 376172",
                "At remaining fuel 9 and original index 376172, selection on the full partial prefix of depth 12 and code 27311 returns the complete row with depth 12, base-four code 27311, original node 376172, kind 2, reserved field 0, 1433 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6815-375295", "unmarked_context_11_6815_375295", "Unmarked parent at depth 11, code 6815",
                "The frontier Boolean is false at remaining fuel 10, original node 375295, the whole prefixCache at depth 11 and code 6815, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1706-376174", "unmarked_context_10_1706_376174", "Unmarked parent at depth 10, code 1706",
                "The frontier Boolean is false at remaining fuel 11, original node 376174, the whole prefixCache at depth 10 and code 1706, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6815-375295", "node_context_11_6815_375295", "Original split at fuel 10 and node 375295",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 375190, 375230, 375259, 375294. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1706-376174", "node_context_10_1706_376174", "Original split at fuel 11 and node 376174",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 376049, 376118, 356516, 376173. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27262-375259", "context_12_27262_375259", "Context at depth 12, code 27262, node 375259",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27262 and original node 375259, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1706-376174", "context_10_1706_376174", "Context at depth 10, code 1706, node 376174",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1706 and original node 376174, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6824_376049, context_11_6825_376118, context_11_6826_356516, context_11_6827_376173.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
