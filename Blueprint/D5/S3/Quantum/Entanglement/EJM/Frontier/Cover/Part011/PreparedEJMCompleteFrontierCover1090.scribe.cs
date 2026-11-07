using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1090Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1090.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1090",
        H("Original frontier context coverage 1090"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52323", "selected_cut_52323", "Selected cut at depth 9, code 18066, node 1523323",
                "At remaining fuel 12 and original index 1523323, selection on the full partial prefix of depth 9 and code 18066 returns the complete row with depth 9, base-four code 18066, original node 1523323, kind 2, reserved field 0, 3825 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52370", "selected_cut_52370", "Selected cut at depth 10, code 72323, node 1525530",
                "At remaining fuel 11 and original index 1525530, selection on the full partial prefix of depth 10 and code 72323 returns the complete row with depth 10, base-four code 72323, original node 1525530, kind 2, reserved field 0, 3057 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18065-1523236", "unmarked_context_9_18065_1523236", "Unmarked parent at depth 9, code 18065",
                "The frontier Boolean is false at remaining fuel 12, original node 1523236, the whole prefixCache at depth 9 and code 18065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-72321-1525310", "unmarked_context_10_72321_1525310", "Unmarked parent at depth 10, code 72321",
                "The frontier Boolean is false at remaining fuel 11, original node 1525310, the whole prefixCache at depth 10 and code 72321, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18065-1523236", "node_context_9_18065_1523236", "Original split at fuel 12 and node 1523236",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1523053, 1468874, 1523163, 1523235. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-72321-1525310", "node_context_10_72321_1525310", "Original split at fuel 11 and node 1525310",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1525106, 1468419, 1525213, 1525309. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18065-1523236", "context_9_18065_1523236", "Context at depth 9, code 18065, node 1523236",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18065 and original node 1523236, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_72260_1523053, context_10_72261_1468874, context_10_72262_1523163, context_10_72263_1523235.", DescribeRole.Theorem),
            Node("context-10-72323-1525530", "context_10_72323_1525530", "Context at depth 10, code 72323, node 1525530",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72323 and original node 1525530, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
