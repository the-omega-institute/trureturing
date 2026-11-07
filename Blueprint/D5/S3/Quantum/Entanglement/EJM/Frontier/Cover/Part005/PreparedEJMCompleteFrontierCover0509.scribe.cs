using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0509Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0509.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0509",
        H("Original frontier context coverage 0509"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24435", "selected_cut_24435", "Selected cut at depth 12, code 77136, node 617543",
                "At remaining fuel 9 and original index 617543, selection on the full partial prefix of depth 12 and code 77136 returns the complete row with depth 12, base-four code 77136, original node 617543, kind 2, reserved field 0, 3885 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24483", "selected_cut_24483", "Selected cut at depth 13, code 308622, node 618471",
                "At remaining fuel 8 and original index 618471, selection on the full partial prefix of depth 13 and code 308622 returns the complete row with depth 13, base-four code 308622, original node 618471, kind 2, reserved field 0, 2145 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4820-617491", "unmarked_context_10_4820_617491", "Unmarked parent at depth 10, code 4820",
                "The frontier Boolean is false at remaining fuel 11, original node 617491, the whole prefixCache at depth 10 and code 4820, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77154-618429", "unmarked_context_12_77154_618429", "Unmarked parent at depth 12, code 77154",
                "The frontier Boolean is false at remaining fuel 9, original node 618429, the whole prefixCache at depth 12 and code 77154, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4820-617491", "node_context_10_4820_617491", "Original split at fuel 11 and node 617491",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 616890, 617055, 617293, 617490. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77154-618429", "node_context_12_77154_618429", "Original split at fuel 9 and node 618429",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 618398, 618419, 618428. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-4820-617491", "context_10_4820_617491", "Context at depth 10, code 4820, node 617491",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4820 and original node 617491, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_19280_616890, context_11_19281_617055, context_11_19282_617293, context_11_19283_617490.", DescribeRole.Theorem),
            Node("context-13-308622-618471", "context_13_308622_618471", "Context at depth 13, code 308622, node 618471",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308622 and original node 618471, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
