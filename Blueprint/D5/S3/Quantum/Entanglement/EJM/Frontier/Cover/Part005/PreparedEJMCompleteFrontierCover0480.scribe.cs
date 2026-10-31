using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0480Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0480.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0480",
        H("Original frontier context coverage 0480"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23043", "selected_cut_23043", "Selected cut at depth 12, code 76107, node 583824",
                "At remaining fuel 9 and original index 583824, selection on the full partial prefix of depth 12 and code 76107 returns the complete row with depth 12, base-four code 76107, original node 583824, kind 2, reserved field 0, 3837 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23090", "selected_cut_23090", "Selected cut at depth 13, code 304511, node 584631",
                "At remaining fuel 8 and original index 584631, selection on the full partial prefix of depth 13 and code 304511 returns the complete row with depth 13, base-four code 304511, original node 584631, kind 2, reserved field 0, 973 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19026-583825", "unmarked_context_11_19026_583825", "Unmarked parent at depth 11, code 19026",
                "The frontier Boolean is false at remaining fuel 10, original node 583825, the whole prefixCache at depth 11 and code 19026, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19031-584633", "unmarked_context_11_19031_584633", "Unmarked parent at depth 11, code 19031",
                "The frontier Boolean is false at remaining fuel 10, original node 584633, the whole prefixCache at depth 11 and code 19031, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19026-583825", "node_context_11_19026_583825", "Original split at fuel 10 and node 583825",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 583695, 583731, 583781, 583824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19031-584633", "node_context_11_19031_584633", "Original split at fuel 10 and node 584633",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 584516, 584551, 584595, 584632. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-76107-583824", "context_12_76107_583824", "Context at depth 12, code 76107, node 583824",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76107 and original node 583824, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-19031-584633", "context_11_19031_584633", "Context at depth 11, code 19031, node 584633",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19031 and original node 584633, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_76124_584516, context_12_76125_584551, context_12_76126_584595, context_12_76127_584632.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
