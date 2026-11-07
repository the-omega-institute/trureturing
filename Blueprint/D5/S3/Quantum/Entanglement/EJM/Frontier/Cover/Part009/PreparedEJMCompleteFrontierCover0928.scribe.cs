using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0928Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0928.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0928",
        H("Original frontier context coverage 0928"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44547", "selected_cut_44547", "Selected cut at depth 11, code 88602, node 900587",
                "At remaining fuel 10 and original index 900587, selection on the full partial prefix of depth 11 and code 88602 returns the complete row with depth 11, base-four code 88602, original node 900587, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44594", "selected_cut_44594", "Selected cut at depth 12, code 354578, node 1227855",
                "At remaining fuel 9 and original index 1227855, selection on the full partial prefix of depth 12 and code 354578 returns the complete row with depth 12, base-four code 354578, original node 1227855, kind 2, reserved field 0, 2449 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22150-1226337", "unmarked_context_10_22150_1226337", "Unmarked parent at depth 10, code 22150",
                "The frontier Boolean is false at remaining fuel 11, original node 1226337, the whole prefixCache at depth 10 and code 22150, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22160-1227763", "unmarked_context_10_22160_1227763", "Unmarked parent at depth 10, code 22160",
                "The frontier Boolean is false at remaining fuel 11, original node 1227763, the whole prefixCache at depth 10 and code 22160, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22150-1226337", "node_context_10_22150_1226337", "Original split at fuel 11 and node 1226337",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1226210, 1226280, 900587, 1226336. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22160-1227763", "node_context_10_22160_1227763", "Original split at fuel 11 and node 1227763",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1227434, 1227620, 1227762. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88602-900587", "context_11_88602_900587", "Context at depth 11, code 88602, node 900587",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88602 and original node 900587, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-354578-1227855", "context_12_354578_1227855", "Context at depth 12, code 354578, node 1227855",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 354578 and original node 1227855, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
