using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0569Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0569.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0569",
        H("Original frontier context coverage 0569"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27316", "selected_cut_27316", "Selected cut at depth 13, code 365821, node 690520",
                "At remaining fuel 8 and original index 690520, selection on the full partial prefix of depth 13 and code 365821 returns the complete row with depth 13, base-four code 365821, original node 690520, kind 2, reserved field 0, 2301 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27363", "selected_cut_27363", "Selected cut at depth 12, code 91503, node 691893",
                "At remaining fuel 9 and original index 691893, selection on the full partial prefix of depth 12 and code 91503 returns the complete row with depth 12, base-four code 91503, original node 691893, kind 2, reserved field 0, 2889 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91455-690550", "unmarked_context_12_91455_690550", "Unmarked parent at depth 12, code 91455",
                "The frontier Boolean is false at remaining fuel 9, original node 690550, the whole prefixCache at depth 12 and code 91455, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22874-691780", "unmarked_context_11_22874_691780", "Unmarked parent at depth 11, code 22874",
                "The frontier Boolean is false at remaining fuel 10, original node 691780, the whole prefixCache at depth 11 and code 22874, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91455-690550", "node_context_12_91455_690550", "Original split at fuel 9 and node 690550",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 690491, 690520, 690540, 690549. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22874-691780", "node_context_11_22874_691780", "Original split at fuel 10 and node 691780",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 691708, 691709, 691740, 691779. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-365821-690520", "context_13_365821_690520", "Context at depth 13, code 365821, node 690520",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 365821 and original node 690520, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91503-691893", "context_12_91503_691893", "Context at depth 12, code 91503, node 691893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91503 and original node 691893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
