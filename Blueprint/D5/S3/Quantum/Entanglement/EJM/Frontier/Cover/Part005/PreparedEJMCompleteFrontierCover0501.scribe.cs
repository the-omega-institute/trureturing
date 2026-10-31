using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0501Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0501.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0501",
        H("Original frontier context coverage 0501"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24052", "selected_cut_24052", "Selected cut at depth 13, code 307432, node 607352",
                "At remaining fuel 8 and original index 607352, selection on the full partial prefix of depth 13 and code 307432 returns the complete row with depth 13, base-four code 307432, original node 607352, kind 2, reserved field 0, 225 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24098", "selected_cut_24098", "Selected cut at depth 13, code 307535, node 608747",
                "At remaining fuel 8 and original index 608747, selection on the full partial prefix of depth 13 and code 307535 returns the complete row with depth 13, base-four code 307535, original node 608747, kind 2, reserved field 0, 773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76857-607346", "unmarked_context_12_76857_607346", "Unmarked parent at depth 12, code 76857",
                "The frontier Boolean is false at remaining fuel 9, original node 607346, the whole prefixCache at depth 12 and code 76857, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76883-608748", "unmarked_context_12_76883_608748", "Unmarked parent at depth 12, code 76883",
                "The frontier Boolean is false at remaining fuel 9, original node 608748, the whole prefixCache at depth 12 and code 76883, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76857-607346", "node_context_12_76857_607346", "Original split at fuel 9 and node 607346",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 607273, 607306, 607338, 607345. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76883-608748", "node_context_12_76883_608748", "Original split at fuel 9 and node 608748",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 608720, 608738, 608747. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76857-607346", "context_12_76857_607346", "Context at depth 12, code 76857, node 607346",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76857 and original node 607346, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_307428_607273, context_13_307429_607306, context_13_307430_607338, context_13_307431_607345.", DescribeRole.Theorem),
            Node("context-12-76883-608748", "context_12_76883_608748", "Context at depth 12, code 76883, node 608748",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76883 and original node 608748, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_307532_3444, context_13_307533_608720, context_13_307534_608738, context_13_307535_608747.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
