using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0312Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0312.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0312",
        H("Original frontier context coverage 0312"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14980", "selected_cut_14980", "Selected cut at depth 13, code 109927, node 385068",
                "At remaining fuel 8 and original index 385068, selection on the full partial prefix of depth 13 and code 109927 returns the complete row with depth 13, base-four code 109927, original node 385068, kind 2, reserved field 0, 1113 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15027", "selected_cut_15027", "Selected cut at depth 13, code 110007, node 386370",
                "At remaining fuel 8 and original index 386370, selection on the full partial prefix of depth 13 and code 110007 returns the complete row with depth 13, base-four code 110007, original node 386370, kind 2, reserved field 0, 1057 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27481-385069", "unmarked_context_12_27481_385069", "Unmarked parent at depth 12, code 27481",
                "The frontier Boolean is false at remaining fuel 9, original node 385069, the whole prefixCache at depth 12 and code 27481, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27501-386371", "unmarked_context_12_27501_386371", "Unmarked parent at depth 12, code 27501",
                "The frontier Boolean is false at remaining fuel 9, original node 386371, the whole prefixCache at depth 12 and code 27501, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27481-385069", "node_context_12_27481_385069", "Original split at fuel 9 and node 385069",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 385027, 385051, 385068. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27501-386371", "node_context_12_27501_386371", "Original split at fuel 9 and node 386371",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 386330, 386354, 386370. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109927-385068", "context_13_109927_385068", "Context at depth 13, code 109927, node 385068",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109927 and original node 385068, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27501-386371", "context_12_27501_386371", "Context at depth 12, code 27501, node 386371",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27501 and original node 386371, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_110004_3444, context_13_110005_386330, context_13_110006_386354, context_13_110007_386370.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
