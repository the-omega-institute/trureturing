using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0567Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0567.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0567",
        H("Original frontier context coverage 0567"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27219", "selected_cut_27219", "Selected cut at depth 13, code 365703, node 688666",
                "At remaining fuel 8 and original index 688666, selection on the full partial prefix of depth 13 and code 365703 returns the complete row with depth 13, base-four code 365703, original node 688666, kind 2, reserved field 0, 729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27266", "selected_cut_27266", "Selected cut at depth 13, code 365759, node 689580",
                "At remaining fuel 8 and original index 689580, selection on the full partial prefix of depth 13 and code 365759 returns the complete row with depth 13, base-four code 365759, original node 689580, kind 2, reserved field 0, 949 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91425-688667", "unmarked_context_12_91425_688667", "Unmarked parent at depth 12, code 91425",
                "The frontier Boolean is false at remaining fuel 9, original node 688667, the whole prefixCache at depth 12 and code 91425, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22859-689582", "unmarked_context_11_22859_689582", "Unmarked parent at depth 11, code 22859",
                "The frontier Boolean is false at remaining fuel 10, original node 689582, the whole prefixCache at depth 11 and code 22859, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91425-688667", "node_context_12_91425_688667", "Original split at fuel 9 and node 688667",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 688619, 688643, 688661, 688666. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22859-689582", "node_context_11_22859_689582", "Original split at fuel 10 and node 689582",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 689374, 689437, 689503, 689581. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-365703-688666", "context_13_365703_688666", "Context at depth 13, code 365703, node 688666",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 365703 and original node 688666, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-22859-689582", "context_11_22859_689582", "Context at depth 11, code 22859, node 689582",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22859 and original node 689582, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_91436_689374, context_12_91437_689437, context_12_91438_689503, context_12_91439_689581.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
