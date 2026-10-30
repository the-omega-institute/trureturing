using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0514Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0514.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0514",
        H("Original frontier context coverage 0514"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24675", "selected_cut_24675", "Selected cut at depth 13, code 309396, node 623770",
                "At remaining fuel 8 and original index 623770, selection on the full partial prefix of depth 13 and code 309396 returns the complete row with depth 13, base-four code 309396, original node 623770, kind 2, reserved field 0, 965 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24722", "selected_cut_24722", "Selected cut at depth 13, code 309455, node 624600",
                "At remaining fuel 8 and original index 624600, selection on the full partial prefix of depth 13 and code 309455 returns the complete row with depth 13, base-four code 309455, original node 624600, kind 2, reserved field 0, 989 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77349-623841", "unmarked_context_12_77349_623841", "Unmarked parent at depth 12, code 77349",
                "The frontier Boolean is false at remaining fuel 9, original node 623841, the whole prefixCache at depth 12 and code 77349, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19340-624602", "unmarked_context_11_19340_624602", "Unmarked parent at depth 11, code 19340",
                "The frontier Boolean is false at remaining fuel 10, original node 624602, the whole prefixCache at depth 11 and code 19340, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77349-623841", "node_context_12_77349_623841", "Original split at fuel 9 and node 623841",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 623770, 623801, 623828, 623840. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19340-624602", "node_context_11_19340_624602", "Original split at fuel 10 and node 624602",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 445562, 624451, 624518, 624601. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-309396-623770", "context_13_309396_623770", "Context at depth 13, code 309396, node 623770",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 309396 and original node 623770, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19340-624602", "context_11_19340_624602", "Context at depth 11, code 19340, node 624602",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19340 and original node 624602, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77360_445562, context_12_77361_624451, context_12_77362_624518, context_12_77363_624601.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
