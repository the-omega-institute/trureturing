using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0259Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0259.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0259",
        H("Original frontier context coverage 0259"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12436", "selected_cut_12436", "Selected cut at depth 13, code 104656, node 328832",
                "At remaining fuel 8 and original index 328832, selection on the full partial prefix of depth 13 and code 104656 returns the complete row with depth 13, base-four code 104656, original node 328832, kind 2, reserved field 0, 437 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12481", "selected_cut_12481", "Selected cut at depth 13, code 104707, node 329646",
                "At remaining fuel 8 and original index 329646, selection on the full partial prefix of depth 13 and code 104707 returns the complete row with depth 13, base-four code 104707, original node 329646, kind 2, reserved field 0, 765 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26163-328825", "unmarked_context_12_26163_328825", "Unmarked parent at depth 12, code 26163",
                "The frontier Boolean is false at remaining fuel 9, original node 328825, the whole prefixCache at depth 12 and code 26163, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26176-329647", "unmarked_context_12_26176_329647", "Unmarked parent at depth 12, code 26176",
                "The frontier Boolean is false at remaining fuel 9, original node 329647, the whole prefixCache at depth 12 and code 26176, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26163-328825", "node_context_12_26163_328825", "Original split at fuel 9 and node 328825",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 328757, 328802, 328819, 328824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26176-329647", "node_context_12_26176_329647", "Original split at fuel 9 and node 329647",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 329619, 329640, 329646. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26163-328825", "context_12_26163_328825", "Context at depth 12, code 26163, node 328825",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26163 and original node 328825, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_104652_328757, context_13_104653_328802, context_13_104654_328819, context_13_104655_328824.", DescribeRole.Theorem),
            Node("context-12-26176-329647", "context_12_26176_329647", "Context at depth 12, code 26176, node 329647",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26176 and original node 329647, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_104704_3444, context_13_104705_329619, context_13_104706_329640, context_13_104707_329646.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
