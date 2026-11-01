using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0540Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0540.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0540",
        H("Original frontier context coverage 0540"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25923", "selected_cut_25923", "Selected cut at depth 13, code 352704, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 352704 returns the complete row with depth 13, base-four code 352704, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25970", "selected_cut_25970", "Selected cut at depth 12, code 88220, node 657212",
                "At remaining fuel 9 and original index 657212, selection on the full partial prefix of depth 12 and code 88220 returns the complete row with depth 12, base-four code 88220, original node 657212, kind 2, reserved field 0, 1957 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5510-655972", "unmarked_context_10_5510_655972", "Unmarked parent at depth 10, code 5510",
                "The frontier Boolean is false at remaining fuel 11, original node 655972, the whole prefixCache at depth 10 and code 5510, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22054-657191", "unmarked_context_11_22054_657191", "Unmarked parent at depth 11, code 22054",
                "The frontier Boolean is false at remaining fuel 10, original node 657191, the whole prefixCache at depth 11 and code 22054, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5510-655972", "node_context_10_5510_655972", "Original split at fuel 11 and node 655972",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 655493, 655603, 655814, 655971. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22054-657191", "node_context_11_22054_657191", "Original split at fuel 10 and node 657191",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 657127, 657147, 657170, 657190. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-5510-655972", "context_10_5510_655972", "Context at depth 10, code 5510, node 655972",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5510 and original node 655972, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_22040_655493, context_11_22041_655603, context_11_22042_655814, context_11_22043_655971.", DescribeRole.Theorem),
            Node("context-12-88220-657212", "context_12_88220_657212", "Context at depth 12, code 88220, node 657212",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88220 and original node 657212, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
