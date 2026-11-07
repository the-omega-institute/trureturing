using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0088Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0088.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0088",
        H("Original frontier context coverage 0088"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04226", "selected_cut_04226", "Selected cut at depth 12, code 18005, node 133683",
                "At remaining fuel 9 and original index 133683, selection on the full partial prefix of depth 12 and code 18005 returns the complete row with depth 12, base-four code 18005, original node 133683, kind 2, reserved field 0, 3537 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04274", "selected_cut_04274", "Selected cut at depth 12, code 18047, node 135594",
                "At remaining fuel 9 and original index 135594, selection on the full partial prefix of depth 12 and code 18047 returns the complete row with depth 12, base-four code 18047, original node 135594, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18006-133787", "unmarked_context_12_18006_133787", "Unmarked parent at depth 12, code 18006",
                "The frontier Boolean is false at remaining fuel 9, original node 133787, the whole prefixCache at depth 12 and code 18006, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4511-135595", "unmarked_context_11_4511_135595", "Unmarked parent at depth 11, code 4511",
                "The frontier Boolean is false at remaining fuel 10, original node 135595, the whole prefixCache at depth 11 and code 4511, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18006-133787", "node_context_12_18006_133787", "Original split at fuel 9 and node 133787",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 133757, 133778, 133786. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4511-135595", "node_context_11_4511_135595", "Original split at fuel 10 and node 135595",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 135490, 135551, 135573, 135594. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18005-133683", "context_12_18005_133683", "Context at depth 12, code 18005, node 133683",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18005 and original node 133683, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-4511-135595", "context_11_4511_135595", "Context at depth 11, code 4511, node 135595",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 4511 and original node 135595, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_18044_135490, context_12_18045_135551, context_12_18046_135573, context_12_18047_135594.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
