using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1085Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1085.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1085",
        H("Original frontier context coverage 1085"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52082", "selected_cut_52082", "Selected cut at depth 9, code 17954, node 1511384",
                "At remaining fuel 12 and original index 1511384, selection on the full partial prefix of depth 9 and code 17954 returns the complete row with depth 9, base-four code 17954, original node 1511384, kind 2, reserved field 0, 977 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52130", "selected_cut_52130", "Selected cut at depth 10, code 71858, node 1513932",
                "At remaining fuel 11 and original index 1513932, selection on the full partial prefix of depth 10 and code 71858 returns the complete row with depth 10, base-four code 71858, original node 1513932, kind 2, reserved field 0, 2269 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-4488-1511436", "unmarked_context_8_4488_1511436", "Unmarked parent at depth 8, code 4488",
                "The frontier Boolean is false at remaining fuel 13, original node 1511436, the whole prefixCache at depth 8 and code 4488, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-71857-1513878", "unmarked_context_10_71857_1513878", "Unmarked parent at depth 10, code 71857",
                "The frontier Boolean is false at remaining fuel 11, original node 1513878, the whole prefixCache at depth 10 and code 71857, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-4488-1511436", "node_context_8_4488_1511436", "Original split at fuel 13 and node 1511436",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1511007, 1511282, 1511384, 1511435. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-71857-1513878", "node_context_10_71857_1513878", "Original split at fuel 11 and node 1513878",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1513689, 1468419, 1513777, 1513877. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-17954-1511384", "context_9_17954_1511384", "Context at depth 9, code 17954, node 1511384",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 17954 and original node 1511384, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-71858-1513932", "context_10_71858_1513932", "Context at depth 10, code 71858, node 1513932",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 71858 and original node 1513932, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
