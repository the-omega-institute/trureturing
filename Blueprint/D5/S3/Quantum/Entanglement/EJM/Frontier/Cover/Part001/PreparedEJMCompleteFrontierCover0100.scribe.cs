using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0100Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0100.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0100",
        H("Original frontier context coverage 0100"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-04804", "selected_cut_04804", "Selected cut at depth 13, code 74992, node 153119",
                "At remaining fuel 8 and original index 153119, selection on the full partial prefix of depth 13 and code 74992 returns the complete row with depth 13, base-four code 74992, original node 153119, kind 2, reserved field 0, 129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-04849", "selected_cut_04849", "Selected cut at depth 13, code 75040, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 75040 returns the complete row with depth 13, base-four code 75040, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-18747-153115", "unmarked_context_12_18747_153115", "Unmarked parent at depth 12, code 18747",
                "The frontier Boolean is false at remaining fuel 9, original node 153115, the whole prefixCache at depth 12 and code 18747, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-4689-153825", "unmarked_context_11_4689_153825", "Unmarked parent at depth 11, code 4689",
                "The frontier Boolean is false at remaining fuel 10, original node 153825, the whole prefixCache at depth 11 and code 4689, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-18747-153115", "node_context_12_18747_153115", "Original split at fuel 9 and node 153115",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 153036, 153076, 153107, 153114. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-4689-153825", "node_context_11_4689_153825", "Original split at fuel 10 and node 153825",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 153693, 126884, 153759, 153824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-18747-153115", "context_12_18747_153115", "Context at depth 12, code 18747, node 153115",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 18747 and original node 153115, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_74988_153036, context_13_74989_153076, context_13_74990_153107, context_13_74991_153114.", DescribeRole.Theorem),
            Node("context-13-75040-3444", "context_13_75040_3444", "Context at depth 13, code 75040, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 75040 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
