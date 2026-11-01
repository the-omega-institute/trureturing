using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0689Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0689.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0689",
        H("Original frontier context coverage 0689"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33075", "selected_cut_33075", "Selected cut at depth 12, code 109953, node 852227",
                "At remaining fuel 9 and original index 852227, selection on the full partial prefix of depth 12 and code 109953 returns the complete row with depth 12, base-four code 109953, original node 852227, kind 2, reserved field 0, 2229 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33123", "selected_cut_33123", "Selected cut at depth 11, code 27510, node 853539",
                "At remaining fuel 10 and original index 853539, selection on the full partial prefix of depth 11 and code 27510 returns the complete row with depth 11, base-four code 27510, original node 853539, kind 2, reserved field 0, 1469 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27488-852257", "unmarked_context_11_27488_852257", "Unmarked parent at depth 11, code 27488",
                "The frontier Boolean is false at remaining fuel 10, original node 852257, the whole prefixCache at depth 11 and code 27488, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6876-853473", "unmarked_context_10_6876_853473", "Unmarked parent at depth 10, code 6876",
                "The frontier Boolean is false at remaining fuel 11, original node 853473, the whole prefixCache at depth 10 and code 6876, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27488-852257", "node_context_11_27488_852257", "Original split at fuel 10 and node 852257",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 852202, 852227, 813440, 852256. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6876-853473", "node_context_10_6876_853473", "Original split at fuel 11 and node 853473",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 853348, 853392, 853428, 853472. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-109953-852227", "context_12_109953_852227", "Context at depth 12, code 109953, node 852227",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109953 and original node 852227, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27510-853539", "context_11_27510_853539", "Context at depth 11, code 27510, node 853539",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27510 and original node 853539, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
