using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0992Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0992.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0992",
        H("Original frontier context coverage 0992"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47619", "selected_cut_47619", "Selected cut at depth 12, code 373812, node 1333241",
                "At remaining fuel 9 and original index 1333241, selection on the full partial prefix of depth 12 and code 373812 returns the complete row with depth 12, base-four code 373812, original node 1333241, kind 2, reserved field 0, 2337 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47666", "selected_cut_47666", "Selected cut at depth 10, code 23375, node 1334615",
                "At remaining fuel 11 and original index 1334615, selection on the full partial prefix of depth 10 and code 23375 returns the complete row with depth 10, base-four code 23375, original node 1334615, kind 2, reserved field 0, 165 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93453-1333319", "unmarked_context_11_93453_1333319", "Unmarked parent at depth 11, code 93453",
                "The frontier Boolean is false at remaining fuel 10, original node 1333319, the whole prefixCache at depth 11 and code 93453, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5843-1334616", "unmarked_context_9_5843_1334616", "Unmarked parent at depth 9, code 5843",
                "The frontier Boolean is false at remaining fuel 12, original node 1334616, the whole prefixCache at depth 9 and code 5843, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93453-1333319", "node_context_11_93453_1333319", "Original split at fuel 10 and node 1333319",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1333241, 1008220, 1333281, 1333318. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5843-1334616", "node_context_9_5843_1334616", "Original split at fuel 12 and node 1334616",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1334525, 1334571, 1334607, 1334615. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-373812-1333241", "context_12_373812_1333241", "Context at depth 12, code 373812, node 1333241",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 373812 and original node 1333241, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-5843-1334616", "context_9_5843_1334616", "Context at depth 9, code 5843, node 1334616",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5843 and original node 1334616, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_23372_1334525, context_10_23373_1334571, context_10_23374_1334607, context_10_23375_1334615.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
