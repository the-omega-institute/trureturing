using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0206Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0206.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0206",
        H("Original frontier context coverage 0206"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09891", "selected_cut_09891", "Selected cut at depth 12, code 24735, node 272285",
                "At remaining fuel 9 and original index 272285, selection on the full partial prefix of depth 12 and code 24735 returns the complete row with depth 12, base-four code 24735, original node 272285, kind 2, reserved field 0, 1925 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09936", "selected_cut_09936", "Selected cut at depth 10, code 1551, node 273131",
                "At remaining fuel 11 and original index 273131, selection on the full partial prefix of depth 10 and code 1551 returns the complete row with depth 10, base-four code 1551, original node 273131, kind 2, reserved field 0, 1577 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6183-272286", "unmarked_context_11_6183_272286", "Unmarked parent at depth 11, code 6183",
                "The frontier Boolean is false at remaining fuel 10, original node 272286, the whole prefixCache at depth 11 and code 6183, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-96-273133", "unmarked_context_8_96_273133", "Unmarked parent at depth 8, code 96",
                "The frontier Boolean is false at remaining fuel 13, original node 273133, the whole prefixCache at depth 8 and code 96, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6183-272286", "node_context_11_6183_272286", "Original split at fuel 10 and node 272286",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 272216, 272240, 272264, 272285. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-96-273133", "node_context_8_96_273133", "Original split at fuel 13 and node 273133",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 268616, 271475, 272832, 273132. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-24735-272285", "context_12_24735_272285", "Context at depth 12, code 24735, node 272285",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 24735 and original node 272285, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-96-273133", "context_8_96_273133", "Context at depth 8, code 96, node 273133",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 96 and original node 273133, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_384_268616, context_9_385_271475, context_9_386_272832, context_9_387_273132.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
