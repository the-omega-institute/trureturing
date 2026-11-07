using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0578Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0578.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0578",
        H("Original frontier context coverage 0578"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27747", "selected_cut_27747", "Selected cut at depth 12, code 91809, node 701113",
                "At remaining fuel 9 and original index 701113, selection on the full partial prefix of depth 12 and code 91809 returns the complete row with depth 12, base-four code 91809, original node 701113, kind 2, reserved field 0, 1353 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27795", "selected_cut_27795", "Selected cut at depth 13, code 367662, node 702576",
                "At remaining fuel 8 and original index 702576, selection on the full partial prefix of depth 13 and code 367662 returns the complete row with depth 13, base-four code 367662, original node 702576, kind 2, reserved field 0, 2477 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22952-701138", "unmarked_context_11_22952_701138", "Unmarked parent at depth 11, code 22952",
                "The frontier Boolean is false at remaining fuel 10, original node 701138, the whole prefixCache at depth 11 and code 22952, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91914-702380", "unmarked_context_12_91914_702380", "Unmarked parent at depth 12, code 91914",
                "The frontier Boolean is false at remaining fuel 9, original node 702380, the whole prefixCache at depth 12 and code 91914, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22952-701138", "node_context_11_22952_701138", "Original split at fuel 10 and node 701138",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 701103, 701113, 701127, 701137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91914-702380", "node_context_12_91914_702380", "Original split at fuel 9 and node 702380",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 702259, 702337, 702368, 702379. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-91809-701113", "context_12_91809_701113", "Context at depth 12, code 91809, node 701113",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91809 and original node 701113, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-367662-702576", "context_13_367662_702576", "Context at depth 13, code 367662, node 702576",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367662 and original node 702576, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
