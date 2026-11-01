using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0524Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0524.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0524",
        H("Original frontier context coverage 0524"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25156", "selected_cut_25156", "Selected cut at depth 13, code 310573, node 635539",
                "At remaining fuel 8 and original index 635539, selection on the full partial prefix of depth 13 and code 310573 returns the complete row with depth 13, base-four code 310573, original node 635539, kind 2, reserved field 0, 2285 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25203", "selected_cut_25203", "Selected cut at depth 13, code 310635, node 636448",
                "At remaining fuel 8 and original index 636448, selection on the full partial prefix of depth 13 and code 310635 returns the complete row with depth 13, base-four code 310635, original node 636448, kind 2, reserved field 0, 869 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77643-635574", "unmarked_context_12_77643_635574", "Unmarked parent at depth 12, code 77643",
                "The frontier Boolean is false at remaining fuel 9, original node 635574, the whole prefixCache at depth 12 and code 77643, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77658-636449", "unmarked_context_12_77658_636449", "Unmarked parent at depth 12, code 77658",
                "The frontier Boolean is false at remaining fuel 9, original node 636449, the whole prefixCache at depth 12 and code 77658, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77643-635574", "node_context_12_77643_635574", "Original split at fuel 9 and node 635574",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 635539, 635561, 635573. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77658-636449", "node_context_12_77658_636449", "Original split at fuel 9 and node 636449",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 636409, 636434, 636448. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-310573-635539", "context_13_310573_635539", "Context at depth 13, code 310573, node 635539",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310573 and original node 635539, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77658-636449", "context_12_77658_636449", "Context at depth 12, code 77658, node 636449",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77658 and original node 636449, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_310632_3444, context_13_310633_636409, context_13_310634_636434, context_13_310635_636448.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
