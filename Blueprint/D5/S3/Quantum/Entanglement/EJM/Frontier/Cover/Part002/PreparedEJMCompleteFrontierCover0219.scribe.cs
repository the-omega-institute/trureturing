using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0219Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0219.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0219",
        H("Original frontier context coverage 0219"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10516", "selected_cut_10516", "Selected cut at depth 12, code 25120, node 285513",
                "At remaining fuel 9 and original index 285513, selection on the full partial prefix of depth 12 and code 25120 returns the complete row with depth 12, base-four code 25120, original node 285513, kind 2, reserved field 0, 3437 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10563", "selected_cut_10563", "Selected cut at depth 13, code 100539, node 286279",
                "At remaining fuel 8 and original index 286279, selection on the full partial prefix of depth 13 and code 100539 returns the complete row with depth 13, base-four code 100539, original node 286279, kind 2, reserved field 0, 729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25119-285464", "unmarked_context_12_25119_285464", "Unmarked parent at depth 12, code 25119",
                "The frontier Boolean is false at remaining fuel 9, original node 285464, the whole prefixCache at depth 12 and code 25119, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25133-286225", "unmarked_context_12_25133_286225", "Unmarked parent at depth 12, code 25133",
                "The frontier Boolean is false at remaining fuel 9, original node 286225, the whole prefixCache at depth 12 and code 25133, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25119-285464", "node_context_12_25119_285464", "Original split at fuel 9 and node 285464",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 285410, 285435, 285454, 285463. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25133-286225", "node_context_12_25133_286225", "Original split at fuel 9 and node 286225",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 286173, 286199, 286219, 286224. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25119-285464", "context_12_25119_285464", "Context at depth 12, code 25119, node 285464",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25119 and original node 285464, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_100476_285410, context_13_100477_285435, context_13_100478_285454, context_13_100479_285463.", DescribeRole.Theorem),
            Node("context-13-100539-286279", "context_13_100539_286279", "Context at depth 13, code 100539, node 286279",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100539 and original node 286279, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
