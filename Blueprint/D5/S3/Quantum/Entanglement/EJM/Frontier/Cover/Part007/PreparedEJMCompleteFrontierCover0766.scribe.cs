using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0766Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0766.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0766",
        H("Original frontier context coverage 0766"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36772", "selected_cut_36772", "Selected cut at depth 11, code 72652, node 977758",
                "At remaining fuel 10 and original index 977758, selection on the full partial prefix of depth 11 and code 72652 returns the complete row with depth 11, base-four code 72652, original node 977758, kind 2, reserved field 0, 2057 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36819", "selected_cut_36819", "Selected cut at depth 10, code 18174, node 979885",
                "At remaining fuel 11 and original index 979885, selection on the full partial prefix of depth 10 and code 18174 returns the complete row with depth 10, base-four code 18174, original node 979885, kind 2, reserved field 0, 617 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-18162-977679", "unmarked_context_10_18162_977679", "Unmarked parent at depth 10, code 18162",
                "The frontier Boolean is false at remaining fuel 11, original node 977679, the whole prefixCache at depth 10 and code 18162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18172-979762", "unmarked_context_10_18172_979762", "Unmarked parent at depth 10, code 18172",
                "The frontier Boolean is false at remaining fuel 11, original node 979762, the whole prefixCache at depth 10 and code 18172, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-18162-977679", "node_context_10_18162_977679", "Original split at fuel 11 and node 977679",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 977307, 977443, 977612, 977678. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18172-979762", "node_context_10_18172_979762", "Original split at fuel 11 and node 979762",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 979642, 979683, 979732, 979761. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18162-977679", "context_10_18162_977679", "Context at depth 10, code 18162, node 977679",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18162 and original node 977679, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_72648_977307, context_11_72649_977443, context_11_72650_977612, context_11_72651_977678.", DescribeRole.Theorem),
            Node("context-10-18174-979885", "context_10_18174_979885", "Context at depth 10, code 18174, node 979885",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18174 and original node 979885, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
