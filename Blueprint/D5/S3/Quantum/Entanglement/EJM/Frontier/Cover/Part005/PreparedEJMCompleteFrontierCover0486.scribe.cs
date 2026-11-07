using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0486Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0486.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0486",
        H("Original frontier context coverage 0486"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23331", "selected_cut_23331", "Selected cut at depth 13, code 305352, node 590679",
                "At remaining fuel 8 and original index 590679, selection on the full partial prefix of depth 13 and code 305352 returns the complete row with depth 13, base-four code 305352, original node 590679, kind 2, reserved field 0, 585 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23377", "selected_cut_23377", "Selected cut at depth 13, code 305407, node 591709",
                "At remaining fuel 8 and original index 591709, selection on the full partial prefix of depth 13 and code 305407 returns the complete row with depth 13, base-four code 305407, original node 591709, kind 2, reserved field 0, 877 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76338-590734", "unmarked_context_12_76338_590734", "Unmarked parent at depth 12, code 76338",
                "The frontier Boolean is false at remaining fuel 9, original node 590734, the whole prefixCache at depth 12 and code 76338, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1192-591713", "unmarked_context_9_1192_591713", "Unmarked parent at depth 9, code 1192",
                "The frontier Boolean is false at remaining fuel 12, original node 591713, the whole prefixCache at depth 9 and code 1192, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76338-590734", "node_context_12_76338_590734", "Original split at fuel 9 and node 590734",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 590679, 590709, 590727, 590733. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1192-591713", "node_context_9_1192_591713", "Original split at fuel 12 and node 591713",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 587825, 589650, 590585, 591712. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-305352-590679", "context_13_305352_590679", "Context at depth 13, code 305352, node 590679",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 305352 and original node 590679, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-1192-591713", "context_9_1192_591713", "Context at depth 9, code 1192, node 591713",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1192 and original node 591713, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_4768_587825, context_10_4769_589650, context_10_4770_590585, context_10_4771_591712.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
