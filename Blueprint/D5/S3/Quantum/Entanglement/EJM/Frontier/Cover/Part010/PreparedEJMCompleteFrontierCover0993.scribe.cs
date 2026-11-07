using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0993Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0993.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0993",
        H("Original frontier context coverage 0993"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47667", "selected_cut_47667", "Selected cut at depth 11, code 93504, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 93504 returns the complete row with depth 11, base-four code 93504, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47715", "selected_cut_47715", "Selected cut at depth 11, code 93519, node 1335968",
                "At remaining fuel 10 and original index 1335968, selection on the full partial prefix of depth 11 and code 93519 returns the complete row with depth 11, base-four code 93519, original node 1335968, kind 2, reserved field 0, 3201 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-1460-1334617", "unmarked_context_8_1460_1334617", "Unmarked parent at depth 8, code 1460",
                "The frontier Boolean is false at remaining fuel 13, original node 1334617, the whole prefixCache at depth 8 and code 1460, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93518-1335909", "unmarked_context_11_93518_1335909", "Unmarked parent at depth 11, code 93518",
                "The frontier Boolean is false at remaining fuel 10, original node 1335909, the whole prefixCache at depth 11 and code 93518, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-1460-1334617", "node_context_8_1460_1334617", "Original split at fuel 13 and node 1334617",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1333452, 1334150, 1334472, 1334616. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93518-1335909", "node_context_11_93518_1335909", "Original split at fuel 10 and node 1335909",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1335830, 1335850, 1335883, 1335908. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-1460-1334617", "context_8_1460_1334617", "Context at depth 8, code 1460, node 1334617",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1460 and original node 1334617, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_5840_1333452, context_9_5841_1334150, context_9_5842_1334472, context_9_5843_1334616.", DescribeRole.Theorem),
            Node("context-11-93519-1335968", "context_11_93519_1335968", "Context at depth 11, code 93519, node 1335968",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93519 and original node 1335968, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
