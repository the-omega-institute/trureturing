using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1096Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1096.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1096",
        H("Original frontier context coverage 1096"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52610", "selected_cut_52610", "Selected cut at depth 10, code 73904, node 1468246",
                "At remaining fuel 11 and original index 1468246, selection on the full partial prefix of depth 10 and code 73904 returns the complete row with depth 10, base-four code 73904, original node 1468246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52657", "selected_cut_52657", "Selected cut at depth 8, code 4660, node 979897",
                "At remaining fuel 13 and original index 979897, selection on the full partial prefix of depth 8 and code 4660 returns the complete row with depth 8, base-four code 4660, original node 979897, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18476-1539944", "unmarked_context_9_18476_1539944", "Unmarked parent at depth 9, code 18476",
                "The frontier Boolean is false at remaining fuel 12, original node 1539944, the whole prefixCache at depth 9 and code 18476, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-1164-1542528", "unmarked_context_7_1164_1542528", "Unmarked parent at depth 7, code 1164",
                "The frontier Boolean is false at remaining fuel 14, original node 1542528, the whole prefixCache at depth 7 and code 1164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18476-1539944", "node_context_9_18476_1539944", "Original split at fuel 12 and node 1539944",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1539832, 1539877, 1539943. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-1164-1542528", "node_context_7_1164_1542528", "Original split at fuel 14 and node 1542528",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1541337, 1541848, 1542250, 1542527. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-73904-1468246", "context_10_73904_1468246", "Context at depth 10, code 73904, node 1468246",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 73904 and original node 1468246, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-4660-979897", "context_8_4660_979897", "Context at depth 8, code 4660, node 979897",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 4660 and original node 979897, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
