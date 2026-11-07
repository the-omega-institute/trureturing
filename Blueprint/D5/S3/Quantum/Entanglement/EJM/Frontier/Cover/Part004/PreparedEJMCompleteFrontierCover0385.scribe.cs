using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0385Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0385.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0385",
        H("Original frontier context coverage 0385"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18482", "selected_cut_18482", "Selected cut at depth 13, code 286853, node 473552",
                "At remaining fuel 8 and original index 473552, selection on the full partial prefix of depth 13 and code 286853 returns the complete row with depth 13, base-four code 286853, original node 473552, kind 2, reserved field 0, 1825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18530", "selected_cut_18530", "Selected cut at depth 13, code 286907, node 474592",
                "At remaining fuel 8 and original index 474592, selection on the full partial prefix of depth 13 and code 286907 returns the complete row with depth 13, base-four code 286907, original node 474592, kind 2, reserved field 0, 829 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-71713-473579", "unmarked_context_12_71713_473579", "Unmarked parent at depth 12, code 71713",
                "The frontier Boolean is false at remaining fuel 9, original node 473579, the whole prefixCache at depth 12 and code 71713, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-71726-474593", "unmarked_context_12_71726_474593", "Unmarked parent at depth 12, code 71726",
                "The frontier Boolean is false at remaining fuel 9, original node 474593, the whole prefixCache at depth 12 and code 71726, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-71713-473579", "node_context_12_71713_473579", "Original split at fuel 9 and node 473579",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 473526, 473552, 473572, 473578. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-71726-474593", "node_context_12_71726_474593", "Original split at fuel 9 and node 474593",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 474527, 474565, 474587, 474592. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-286853-473552", "context_13_286853_473552", "Context at depth 13, code 286853, node 473552",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 286853 and original node 473552, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71726-474593", "context_12_71726_474593", "Context at depth 12, code 71726, node 474593",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71726 and original node 474593, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_286904_474527, context_13_286905_474565, context_13_286906_474587, context_13_286907_474592.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
