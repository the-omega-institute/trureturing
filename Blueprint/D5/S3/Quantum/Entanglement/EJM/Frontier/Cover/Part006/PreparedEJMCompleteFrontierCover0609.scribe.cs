using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0609Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0609.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0609",
        H("Original frontier context coverage 0609"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29235", "selected_cut_29235", "Selected cut at depth 13, code 373800, node 738764",
                "At remaining fuel 8 and original index 738764, selection on the full partial prefix of depth 13 and code 373800 returns the complete row with depth 13, base-four code 373800, original node 738764, kind 2, reserved field 0, 2905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-29282", "selected_cut_29282", "Selected cut at depth 13, code 373859, node 739929",
                "At remaining fuel 8 and original index 739929, selection on the full partial prefix of depth 13 and code 373859 returns the complete row with depth 13, base-four code 373859, original node 739929, kind 2, reserved field 0, 757 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93450-738897", "unmarked_context_12_93450_738897", "Unmarked parent at depth 12, code 93450",
                "The frontier Boolean is false at remaining fuel 9, original node 738897, the whole prefixCache at depth 12 and code 93450, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93464-739930", "unmarked_context_12_93464_739930", "Unmarked parent at depth 12, code 93464",
                "The frontier Boolean is false at remaining fuel 9, original node 739930, the whole prefixCache at depth 12 and code 93464, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93450-738897", "node_context_12_93450_738897", "Original split at fuel 9 and node 738897",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 738764, 738813, 738869, 738896. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93464-739930", "node_context_12_93464_739930", "Original split at fuel 9 and node 739930",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 739883, 739904, 739921, 739929. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-373800-738764", "context_13_373800_738764", "Context at depth 13, code 373800, node 738764",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 373800 and original node 738764, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93464-739930", "context_12_93464_739930", "Context at depth 12, code 93464, node 739930",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93464 and original node 739930, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_373856_739883, context_13_373857_739904, context_13_373858_739921, context_13_373859_739929.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
