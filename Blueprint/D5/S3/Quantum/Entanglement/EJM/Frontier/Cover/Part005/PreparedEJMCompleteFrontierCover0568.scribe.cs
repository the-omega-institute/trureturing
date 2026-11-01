using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0568Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0568.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0568",
        H("Original frontier context coverage 0568"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27267", "selected_cut_27267", "Selected cut at depth 13, code 365760, node 689598",
                "At remaining fuel 8 and original index 689598, selection on the full partial prefix of depth 13 and code 365760 returns the complete row with depth 13, base-four code 365760, original node 689598, kind 2, reserved field 0, 825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27315", "selected_cut_27315", "Selected cut at depth 13, code 365820, node 690491",
                "At remaining fuel 8 and original index 690491, selection on the full partial prefix of depth 13 and code 365820 returns the complete row with depth 13, base-four code 365820, original node 690491, kind 2, reserved field 0, 77 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5714-689583", "unmarked_context_10_5714_689583", "Unmarked parent at depth 10, code 5714",
                "The frontier Boolean is false at remaining fuel 11, original node 689583, the whole prefixCache at depth 10 and code 5714, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91454-690487", "unmarked_context_12_91454_690487", "Unmarked parent at depth 12, code 91454",
                "The frontier Boolean is false at remaining fuel 9, original node 690487, the whole prefixCache at depth 12 and code 91454, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5714-689583", "node_context_10_5714_689583", "Original split at fuel 11 and node 689583",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 688840, 689033, 689310, 689582. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91454-690487", "node_context_12_91454_690487", "Original split at fuel 9 and node 690487",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 690435, 690459, 690477, 690486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-5714-689583", "context_10_5714_689583", "Context at depth 10, code 5714, node 689583",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5714 and original node 689583, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_22856_688840, context_11_22857_689033, context_11_22858_689310, context_11_22859_689582.", DescribeRole.Theorem),
            Node("context-13-365820-690491", "context_13_365820_690491", "Context at depth 13, code 365820, node 690491",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 365820 and original node 690491, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
