using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0426Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0426.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0426",
        H("Original frontier context coverage 0426"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20451", "selected_cut_20451", "Selected cut at depth 13, code 296046, node 525319",
                "At remaining fuel 8 and original index 525319, selection on the full partial prefix of depth 13 and code 296046 returns the complete row with depth 13, base-four code 296046, original node 525319, kind 2, reserved field 0, 1369 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20497", "selected_cut_20497", "Selected cut at depth 13, code 296095, node 526182",
                "At remaining fuel 8 and original index 526182, selection on the full partial prefix of depth 13 and code 296095 returns the complete row with depth 13, base-four code 296095, original node 526182, kind 2, reserved field 0, 637 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74011-525323", "unmarked_context_12_74011_525323", "Unmarked parent at depth 12, code 74011",
                "The frontier Boolean is false at remaining fuel 9, original node 525323, the whole prefixCache at depth 12 and code 74011, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18505-526184", "unmarked_context_11_18505_526184", "Unmarked parent at depth 11, code 18505",
                "The frontier Boolean is false at remaining fuel 10, original node 526184, the whole prefixCache at depth 11 and code 18505, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74011-525323", "node_context_12_74011_525323", "Original split at fuel 9 and node 525323",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 525277, 525301, 525319, 525322. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18505-526184", "node_context_11_18505_526184", "Original split at fuel 10 and node 526184",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 525925, 526032, 526102, 526183. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-296046-525319", "context_13_296046_525319", "Context at depth 13, code 296046, node 525319",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 296046 and original node 525319, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-18505-526184", "context_11_18505_526184", "Context at depth 11, code 18505, node 526184",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18505 and original node 526184, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_74020_525925, context_12_74021_526032, context_12_74022_526102, context_12_74023_526183.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
