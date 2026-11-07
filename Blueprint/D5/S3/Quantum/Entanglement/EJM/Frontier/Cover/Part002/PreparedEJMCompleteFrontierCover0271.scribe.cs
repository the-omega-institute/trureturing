using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0271Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0271.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0271",
        H("Original frontier context coverage 0271"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13012", "selected_cut_13012", "Selected cut at depth 13, code 105790, node 342332",
                "At remaining fuel 8 and original index 342332, selection on the full partial prefix of depth 13 and code 105790 returns the complete row with depth 13, base-four code 105790, original node 342332, kind 2, reserved field 0, 2601 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13058", "selected_cut_13058", "Selected cut at depth 13, code 105863, node 343549",
                "At remaining fuel 8 and original index 343549, selection on the full partial prefix of depth 13 and code 105863 returns the complete row with depth 13, base-four code 105863, original node 343549, kind 2, reserved field 0, 1017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26447-342363", "unmarked_context_12_26447_342363", "Unmarked parent at depth 12, code 26447",
                "The frontier Boolean is false at remaining fuel 9, original node 342363, the whole prefixCache at depth 12 and code 26447, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26465-343550", "unmarked_context_12_26465_343550", "Unmarked parent at depth 12, code 26465",
                "The frontier Boolean is false at remaining fuel 9, original node 343550, the whole prefixCache at depth 12 and code 26465, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26447-342363", "node_context_12_26447_342363", "Original split at fuel 9 and node 342363",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 342284, 342332, 342362. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26465-343550", "node_context_12_26465_343550", "Original split at fuel 9 and node 343550",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 343485, 343540, 343549. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105790-342332", "context_13_105790_342332", "Context at depth 13, code 105790, node 342332",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105790 and original node 342332, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-26465-343550", "context_12_26465_343550", "Context at depth 12, code 26465, node 343550",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26465 and original node 343550, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_105860_3444, context_13_105861_343485, context_13_105862_343540, context_13_105863_343549.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
