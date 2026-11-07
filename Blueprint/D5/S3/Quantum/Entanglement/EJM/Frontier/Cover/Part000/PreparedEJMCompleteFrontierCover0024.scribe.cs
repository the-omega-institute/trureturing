using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0024Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0024.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0024",
        H("Original frontier context coverage 0024"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01154", "selected_cut_01154", "Selected cut at depth 13, code 17672, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 17672 returns the complete row with depth 13, base-four code 17672, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01201", "selected_cut_01201", "Selected cut at depth 13, code 17752, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 17752 returns the complete row with depth 13, base-four code 17752, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4417-44268", "unmarked_context_12_4417_44268", "Unmarked parent at depth 12, code 4417",
                "The frontier Boolean is false at remaining fuel 9, original node 44268, the whole prefixCache at depth 12 and code 4417, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4437-45152", "unmarked_context_12_4437_45152", "Unmarked parent at depth 12, code 4437",
                "The frontier Boolean is false at remaining fuel 9, original node 45152, the whole prefixCache at depth 12 and code 4437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4417-44268", "node_context_12_4417_44268", "Original split at fuel 9 and node 44268",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 44219, 44267, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4437-45152", "node_context_12_4437_45152", "Original split at fuel 9 and node 45152",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 45106, 45151, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4417-44268", "context_12_4417_44268", "Context at depth 12, code 4417, node 44268",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4417 and original node 44268, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_17668_3444, context_13_17669_44219, context_13_17670_44267, context_13_17671_414.", DescribeRole.Theorem),
            Node("context-13-17752-3444", "context_13_17752_3444", "Context at depth 13, code 17752, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17752 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
