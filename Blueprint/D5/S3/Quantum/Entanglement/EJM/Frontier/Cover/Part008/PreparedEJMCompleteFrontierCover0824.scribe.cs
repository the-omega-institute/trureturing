using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0824Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0824.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0824",
        H("Original frontier context coverage 0824"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39555", "selected_cut_39555", "Selected cut at depth 12, code 307488, node 1072955",
                "At remaining fuel 9 and original index 1072955, selection on the full partial prefix of depth 12 and code 307488 returns the complete row with depth 12, base-four code 307488, original node 1072955, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39602", "selected_cut_39602", "Selected cut at depth 12, code 307553, node 1074947",
                "At remaining fuel 9 and original index 1074947, selection on the full partial prefix of depth 12 and code 307553 returns the complete row with depth 12, base-four code 307553, original node 1074947, kind 2, reserved field 0, 1681 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-19217-1073548", "unmarked_context_10_19217_1073548", "Unmarked parent at depth 10, code 19217",
                "The frontier Boolean is false at remaining fuel 11, original node 1073548, the whole prefixCache at depth 10 and code 19217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-19220-1074911", "unmarked_context_10_19220_1074911", "Unmarked parent at depth 10, code 19220",
                "The frontier Boolean is false at remaining fuel 11, original node 1074911, the whole prefixCache at depth 10 and code 19220, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-19217-1073548", "node_context_10_19217_1073548", "Original split at fuel 11 and node 1073548",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1073055, 1073186, 1073345, 1073547. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-19220-1074911", "node_context_10_19220_1074911", "Original split at fuel 11 and node 1074911",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1074646, 1074777, 1074910. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-19217-1073548", "context_10_19217_1073548", "Context at depth 10, code 19217, node 1073548",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 19217 and original node 1073548, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_76868_1073055, context_11_76869_1073186, context_11_76870_1073345, context_11_76871_1073547.", DescribeRole.Theorem),
            Node("context-12-307553-1074947", "context_12_307553_1074947", "Context at depth 12, code 307553, node 1074947",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307553 and original node 1074947, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
