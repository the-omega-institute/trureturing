using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1099Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1099.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1099",
        H("Original frontier context coverage 1099"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52754", "selected_cut_52754", "Selected cut at depth 9, code 18881, node 1549228",
                "At remaining fuel 12 and original index 1549228, selection on the full partial prefix of depth 9 and code 18881 returns the complete row with depth 9, base-four code 18881, original node 1549228, kind 2, reserved field 0, 1277 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52803", "selected_cut_52803", "Selected cut at depth 9, code 18927, node 1553051",
                "At remaining fuel 12 and original index 1553051, selection on the full partial prefix of depth 9 and code 18927 returns the complete row with depth 9, base-four code 18927, original node 1553051, kind 2, reserved field 0, 77 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-4720-1549308", "unmarked_context_8_4720_1549308", "Unmarked parent at depth 8, code 4720",
                "The frontier Boolean is false at remaining fuel 13, original node 1549308, the whole prefixCache at depth 8 and code 4720, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-18924-1552817", "unmarked_context_9_18924_1552817", "Unmarked parent at depth 9, code 18924",
                "The frontier Boolean is false at remaining fuel 12, original node 1552817, the whole prefixCache at depth 9 and code 18924, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-4720-1549308", "node_context_8_4720_1549308", "Original split at fuel 13 and node 1549308",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1549163, 1549228, 1549281, 1549307. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-18924-1552817", "node_context_9_18924_1552817", "Original split at fuel 12 and node 1552817",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1552665, 1552741, 1552816. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18881-1549228", "context_9_18881_1549228", "Context at depth 9, code 18881, node 1549228",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18881 and original node 1549228, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-18927-1553051", "context_9_18927_1553051", "Context at depth 9, code 18927, node 1553051",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18927 and original node 1553051, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
