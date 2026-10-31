using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0817Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0817.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0817",
        H("Original frontier context coverage 0817"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39220", "selected_cut_39220", "Selected cut at depth 12, code 302707, node 1063542",
                "At remaining fuel 9 and original index 1063542, selection on the full partial prefix of depth 12 and code 302707 returns the complete row with depth 12, base-four code 302707, original node 1063542, kind 2, reserved field 0, 1777 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39267", "selected_cut_39267", "Selected cut at depth 10, code 18927, node 1064722",
                "At remaining fuel 11 and original index 1064722, selection on the full partial prefix of depth 10 and code 18927 returns the complete row with depth 10, base-four code 18927, original node 1064722, kind 2, reserved field 0, 609 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75676-1063543", "unmarked_context_11_75676_1063543", "Unmarked parent at depth 11, code 75676",
                "The frontier Boolean is false at remaining fuel 10, original node 1063543, the whole prefixCache at depth 11 and code 75676, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18925-1064640", "unmarked_context_10_18925_1064640", "Unmarked parent at depth 10, code 18925",
                "The frontier Boolean is false at remaining fuel 11, original node 1064640, the whole prefixCache at depth 10 and code 18925, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75676-1063543", "node_context_11_75676_1063543", "Original split at fuel 10 and node 1063543",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1063462, 1063491, 1063517, 1063542. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18925-1064640", "node_context_10_18925_1064640", "Original split at fuel 11 and node 1064640",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1064598, 1064615, 1064631, 1064639. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302707-1063542", "context_12_302707_1063542", "Context at depth 12, code 302707, node 1063542",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302707 and original node 1063542, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-18927-1064722", "context_10_18927_1064722", "Context at depth 10, code 18927, node 1064722",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18927 and original node 1064722, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
