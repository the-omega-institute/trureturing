using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0234Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0234.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0234",
        H("Original frontier context coverage 0234"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11236", "selected_cut_11236", "Selected cut at depth 12, code 25528, node 301205",
                "At remaining fuel 9 and original index 301205, selection on the full partial prefix of depth 12 and code 25528 returns the complete row with depth 12, base-four code 25528, original node 301205, kind 2, reserved field 0, 1201 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11281", "selected_cut_11281", "Selected cut at depth 13, code 102433, node 302610",
                "At remaining fuel 8 and original index 302610, selection on the full partial prefix of depth 13 and code 102433 returns the complete row with depth 13, base-four code 102433, original node 302610, kind 2, reserved field 0, 3821 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6381-301194", "unmarked_context_11_6381_301194", "Unmarked parent at depth 11, code 6381",
                "The frontier Boolean is false at remaining fuel 10, original node 301194, the whole prefixCache at depth 11 and code 6381, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6401-302487", "unmarked_context_11_6401_302487", "Unmarked parent at depth 11, code 6401",
                "The frontier Boolean is false at remaining fuel 10, original node 302487, the whole prefixCache at depth 11 and code 6401, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6381-301194", "node_context_11_6381_301194", "Original split at fuel 10 and node 301194",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 301155, 301173, 301184, 301193. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6401-302487", "node_context_11_6401_302487", "Original split at fuel 10 and node 302487",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 34034, 302193, 302326, 302486. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6381-301194", "context_11_6381_301194", "Context at depth 11, code 6381, node 301194",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6381 and original node 301194, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_25524_301155, context_12_25525_301173, context_12_25526_301184, context_12_25527_301193.", DescribeRole.Theorem),
            Node("context-13-102433-302610", "context_13_102433_302610", "Context at depth 13, code 102433, node 302610",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102433 and original node 302610, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
