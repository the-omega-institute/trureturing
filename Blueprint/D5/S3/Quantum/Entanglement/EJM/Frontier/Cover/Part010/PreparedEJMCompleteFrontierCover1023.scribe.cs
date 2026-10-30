using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1023Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1023.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1023",
        H("Original frontier context coverage 1023"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49107", "selected_cut_49107", "Selected cut at depth 9, code 6342, node 1386941",
                "At remaining fuel 12 and original index 1386941, selection on the full partial prefix of depth 9 and code 6342 returns the complete row with depth 9, base-four code 6342, original node 1386941, kind 2, reserved field 0, 2069 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49154", "selected_cut_49154", "Selected cut at depth 11, code 101543, node 1388719",
                "At remaining fuel 10 and original index 1388719, selection on the full partial prefix of depth 11 and code 101543 returns the complete row with depth 11, base-four code 101543, original node 1388719, kind 2, reserved field 0, 1717 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6341-1386852", "unmarked_context_9_6341_1386852", "Unmarked parent at depth 9, code 6341",
                "The frontier Boolean is false at remaining fuel 12, original node 1386852, the whole prefixCache at depth 9 and code 6341, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25385-1388720", "unmarked_context_10_25385_1388720", "Unmarked parent at depth 10, code 25385",
                "The frontier Boolean is false at remaining fuel 11, original node 1388720, the whole prefixCache at depth 10 and code 25385, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6341-1386852", "node_context_9_6341_1386852", "Original split at fuel 12 and node 1386852",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 793297, 893098, 1386697, 1386851. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25385-1388720", "node_context_10_25385_1388720", "Original split at fuel 11 and node 1388720",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1388636, 1388656, 1388679, 1388719. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-6341-1386852", "context_9_6341_1386852", "Context at depth 9, code 6341, node 1386852",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6341 and original node 1386852, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_25364_793297, context_10_25365_893098, context_10_25366_1386697, context_10_25367_1386851.", DescribeRole.Theorem),
            Node("context-10-25385-1388720", "context_10_25385_1388720", "Context at depth 10, code 25385, node 1388720",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25385 and original node 1388720, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_101540_1388636, context_11_101541_1388656, context_11_101542_1388679, context_11_101543_1388719.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
