using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0682Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0682.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0682",
        H("Original frontier context coverage 0682"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32740", "selected_cut_32740", "Selected cut at depth 12, code 109678, node 842963",
                "At remaining fuel 9 and original index 842963, selection on the full partial prefix of depth 12 and code 109678 returns the complete row with depth 12, base-four code 109678, original node 842963, kind 2, reserved field 0, 2917 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32786", "selected_cut_32786", "Selected cut at depth 12, code 109727, node 844290",
                "At remaining fuel 9 and original index 844290, selection on the full partial prefix of depth 12 and code 109727 returns the complete row with depth 12, base-four code 109727, original node 844290, kind 2, reserved field 0, 1833 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27419-843010", "unmarked_context_11_27419_843010", "Unmarked parent at depth 11, code 27419",
                "The frontier Boolean is false at remaining fuel 10, original node 843010, the whole prefixCache at depth 11 and code 27419, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6857-844292", "unmarked_context_10_6857_844292", "Unmarked parent at depth 10, code 6857",
                "The frontier Boolean is false at remaining fuel 11, original node 844292, the whole prefixCache at depth 10 and code 6857, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27419-843010", "node_context_11_27419_843010", "Original split at fuel 10 and node 843010",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 842881, 842926, 842963, 843009. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6857-844292", "node_context_10_6857_844292", "Original split at fuel 11 and node 844292",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 843948, 844057, 844176, 844291. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-109678-842963", "context_12_109678_842963", "Context at depth 12, code 109678, node 842963",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109678 and original node 842963, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-6857-844292", "context_10_6857_844292", "Context at depth 10, code 6857, node 844292",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 6857 and original node 844292, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_27428_843948, context_11_27429_844057, context_11_27430_844176, context_11_27431_844291.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
