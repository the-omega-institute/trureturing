using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0701Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0701.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0701",
        H("Original frontier context coverage 0701"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33653", "selected_cut_33653", "Selected cut at depth 13, code 441572, node 866283",
                "At remaining fuel 8 and original index 866283, selection on the full partial prefix of depth 13 and code 441572 returns the complete row with depth 13, base-four code 441572, original node 866283, kind 2, reserved field 0, 125 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33699", "selected_cut_33699", "Selected cut at depth 13, code 441633, node 867123",
                "At remaining fuel 8 and original index 867123, selection on the full partial prefix of depth 13 and code 441633 returns the complete row with depth 13, base-four code 441633, original node 867123, kind 2, reserved field 0, 3017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110392-866280", "unmarked_context_12_110392_866280", "Unmarked parent at depth 12, code 110392",
                "The frontier Boolean is false at remaining fuel 9, original node 866280, the whole prefixCache at depth 12 and code 110392, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27601-867069", "unmarked_context_11_27601_867069", "Unmarked parent at depth 11, code 27601",
                "The frontier Boolean is false at remaining fuel 10, original node 867069, the whole prefixCache at depth 11 and code 27601, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110392-866280", "node_context_12_110392_866280", "Original split at fuel 9 and node 866280",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 866176, 866233, 866273, 866279. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27601-867069", "node_context_11_27601_867069", "Original split at fuel 10 and node 867069",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 866852, 866919, 866996, 867068. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-110392-866280", "context_12_110392_866280", "Context at depth 12, code 110392, node 866280",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110392 and original node 866280, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_441568_866176, context_13_441569_866233, context_13_441570_866273, context_13_441571_866279.", DescribeRole.Theorem),
            Node("context-13-441633-867123", "context_13_441633_867123", "Context at depth 13, code 441633, node 867123",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 441633 and original node 867123, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
