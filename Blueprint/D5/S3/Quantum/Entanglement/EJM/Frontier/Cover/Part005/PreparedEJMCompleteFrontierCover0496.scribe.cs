using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0496Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0496.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0496",
        H("Original frontier context coverage 0496"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23813", "selected_cut_23813", "Selected cut at depth 12, code 76652, node 601365",
                "At remaining fuel 9 and original index 601365, selection on the full partial prefix of depth 12 and code 76652 returns the complete row with depth 12, base-four code 76652, original node 601365, kind 2, reserved field 0, 2701 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23859", "selected_cut_23859", "Selected cut at depth 12, code 76695, node 602706",
                "At remaining fuel 9 and original index 602706, selection on the full partial prefix of depth 12 and code 76695 returns the complete row with depth 12, base-four code 76695, original node 602706, kind 2, reserved field 0, 2041 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76651-601329", "unmarked_context_12_76651_601329", "Unmarked parent at depth 12, code 76651",
                "The frontier Boolean is false at remaining fuel 9, original node 601329, the whole prefixCache at depth 12 and code 76651, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19172-602602", "unmarked_context_11_19172_602602", "Unmarked parent at depth 11, code 19172",
                "The frontier Boolean is false at remaining fuel 10, original node 602602, the whole prefixCache at depth 11 and code 19172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76651-601329", "node_context_12_76651_601329", "Original split at fuel 9 and node 601329",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 601287, 601321, 601328. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19172-602602", "node_context_11_19172_602602", "Original split at fuel 10 and node 602602",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 602521, 602546, 602585, 602601. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76651-601329", "context_12_76651_601329", "Context at depth 12, code 76651, node 601329",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76651 and original node 601329, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_306604_3444, context_13_306605_601287, context_13_306606_601321, context_13_306607_601328.", DescribeRole.Theorem),
            Node("context-12-76695-602706", "context_12_76695_602706", "Context at depth 12, code 76695, node 602706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76695 and original node 602706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
