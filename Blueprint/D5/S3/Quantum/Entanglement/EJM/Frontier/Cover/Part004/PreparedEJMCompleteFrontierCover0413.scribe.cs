using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0413Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0413.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0413",
        H("Original frontier context coverage 0413"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19827", "selected_cut_19827", "Selected cut at depth 10, code 4527, node 507051",
                "At remaining fuel 11 and original index 507051, selection on the full partial prefix of depth 10 and code 4527 returns the complete row with depth 10, base-four code 4527, original node 507051, kind 2, reserved field 0, 1549 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19874", "selected_cut_19874", "Selected cut at depth 13, code 289871, node 508767",
                "At remaining fuel 8 and original index 508767, selection on the full partial prefix of depth 13 and code 289871 returns the complete row with depth 13, base-four code 289871, original node 508767, kind 2, reserved field 0, 577 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-1131-507052", "unmarked_context_9_1131_507052", "Unmarked parent at depth 9, code 1131",
                "The frontier Boolean is false at remaining fuel 12, original node 507052, the whole prefixCache at depth 9 and code 1131, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72467-508768", "unmarked_context_12_72467_508768", "Unmarked parent at depth 12, code 72467",
                "The frontier Boolean is false at remaining fuel 9, original node 508768, the whole prefixCache at depth 12 and code 72467, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-1131-507052", "node_context_9_1131_507052", "Original split at fuel 12 and node 507052",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 506730, 506948, 507009, 507051. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72467-508768", "node_context_12_72467_508768", "Original split at fuel 9 and node 508768",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 508708, 508738, 508760, 508767. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-4527-507051", "context_10_4527_507051", "Context at depth 10, code 4527, node 507051",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4527 and original node 507051, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-72467-508768", "context_12_72467_508768", "Context at depth 12, code 72467, node 508768",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 72467 and original node 508768, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_289868_508708, context_13_289869_508738, context_13_289870_508760, context_13_289871_508767.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
