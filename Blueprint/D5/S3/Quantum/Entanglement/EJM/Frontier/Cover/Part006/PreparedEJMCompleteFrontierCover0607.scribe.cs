using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0607Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0607.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0607",
        H("Original frontier context coverage 0607"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29140", "selected_cut_29140", "Selected cut at depth 13, code 373237, node 735907",
                "At remaining fuel 8 and original index 735907, selection on the full partial prefix of depth 13 and code 373237 returns the complete row with depth 13, base-four code 373237, original node 735907, kind 2, reserved field 0, 253 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29187", "selected_cut_29187", "Selected cut at depth 12, code 93354, node 737472",
                "At remaining fuel 9 and original index 737472, selection on the full partial prefix of depth 12 and code 93354 returns the complete row with depth 12, base-four code 93354, original node 737472, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93309-736017", "unmarked_context_12_93309_736017", "Unmarked parent at depth 12, code 93309",
                "The frontier Boolean is false at remaining fuel 9, original node 736017, the whole prefixCache at depth 12 and code 93309, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23337-737419", "unmarked_context_11_23337_737419", "Unmarked parent at depth 11, code 23337",
                "The frontier Boolean is false at remaining fuel 10, original node 737419, the whole prefixCache at depth 11 and code 23337, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93309-736017", "node_context_12_93309_736017", "Original split at fuel 9 and node 736017",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 735907, 735992, 736016. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23337-737419", "node_context_11_23337_737419", "Original split at fuel 10 and node 737419",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 737351, 737373, 737400, 737418. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-373237-735907", "context_13_373237_735907", "Context at depth 13, code 373237, node 735907",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 373237 and original node 735907, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93354-737472", "context_12_93354_737472", "Context at depth 12, code 93354, node 737472",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93354 and original node 737472, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
