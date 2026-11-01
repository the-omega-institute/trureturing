using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0591Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0591.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0591",
        H("Original frontier context coverage 0591"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28371", "selected_cut_28371", "Selected cut at depth 13, code 369735, node 717118",
                "At remaining fuel 8 and original index 717118, selection on the full partial prefix of depth 13 and code 369735 returns the complete row with depth 13, base-four code 369735, original node 717118, kind 2, reserved field 0, 709 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28419", "selected_cut_28419", "Selected cut at depth 13, code 369786, node 717888",
                "At remaining fuel 8 and original index 717888, selection on the full partial prefix of depth 13 and code 369786 returns the complete row with depth 13, base-four code 369786, original node 717888, kind 2, reserved field 0, 1325 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92433-717119", "unmarked_context_12_92433_717119", "Unmarked parent at depth 12, code 92433",
                "The frontier Boolean is false at remaining fuel 9, original node 717119, the whole prefixCache at depth 12 and code 92433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92445-717832", "unmarked_context_12_92445_717832", "Unmarked parent at depth 12, code 92445",
                "The frontier Boolean is false at remaining fuel 9, original node 717832, the whole prefixCache at depth 12 and code 92445, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92433-717119", "node_context_12_92433_717119", "Original split at fuel 9 and node 717119",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 717075, 717094, 717110, 717118. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92445-717832", "node_context_12_92445_717832", "Original split at fuel 9 and node 717832",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 717791, 717811, 717826, 717831. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-369735-717118", "context_13_369735_717118", "Context at depth 13, code 369735, node 717118",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369735 and original node 717118, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-369786-717888", "context_13_369786_717888", "Context at depth 13, code 369786, node 717888",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369786 and original node 717888, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
