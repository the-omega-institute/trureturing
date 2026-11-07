using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1052Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1052.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1052",
        H("Original frontier context coverage 1052"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50499", "selected_cut_50499", "Selected cut at depth 11, code 106320, node 1443364",
                "At remaining fuel 10 and original index 1443364, selection on the full partial prefix of depth 11 and code 106320 returns the complete row with depth 11, base-four code 106320, original node 1443364, kind 2, reserved field 0, 1365 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50547", "selected_cut_50547", "Selected cut at depth 11, code 106383, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 106383 returns the complete row with depth 11, base-four code 106383, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-26580-1443555", "unmarked_context_10_26580_1443555", "Unmarked parent at depth 10, code 26580",
                "The frontier Boolean is false at remaining fuel 11, original node 1443555, the whole prefixCache at depth 10 and code 26580, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-26595-1445305", "unmarked_context_10_26595_1445305", "Unmarked parent at depth 10, code 26595",
                "The frontier Boolean is false at remaining fuel 11, original node 1445305, the whole prefixCache at depth 10 and code 26595, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-26580-1443555", "node_context_10_26580_1443555", "Original split at fuel 11 and node 1443555",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1443364, 1443442, 1443501, 1443554. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-26595-1445305", "node_context_10_26595_1445305", "Original split at fuel 11 and node 1445305",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1445171, 1445230, 1445304, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-106320-1443364", "context_11_106320_1443364", "Context at depth 11, code 106320, node 1443364",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106320 and original node 1443364, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-26595-1445305", "context_10_26595_1445305", "Context at depth 10, code 26595, node 1445305",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 26595 and original node 1445305, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_106380_1445171, context_11_106381_1445230, context_11_106382_1445304, context_11_106383_977886.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
