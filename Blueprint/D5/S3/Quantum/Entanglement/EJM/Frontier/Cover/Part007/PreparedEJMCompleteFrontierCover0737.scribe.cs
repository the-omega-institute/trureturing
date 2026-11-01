using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0737Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0737.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0737",
        H("Original frontier context coverage 0737"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35379", "selected_cut_35379", "Selected cut at depth 12, code 285456, node 106538",
                "At remaining fuel 9 and original index 106538, selection on the full partial prefix of depth 12 and code 285456 returns the complete row with depth 12, base-four code 285456, original node 106538, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35426", "selected_cut_35426", "Selected cut at depth 12, code 285572, node 931082",
                "At remaining fuel 9 and original index 931082, selection on the full partial prefix of depth 12 and code 285572 returns the complete row with depth 12, base-four code 285572, original node 931082, kind 2, reserved field 0, 1345 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17840-929517", "unmarked_context_10_17840_929517", "Unmarked parent at depth 10, code 17840",
                "The frontier Boolean is false at remaining fuel 11, original node 929517, the whole prefixCache at depth 10 and code 17840, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71392-931060", "unmarked_context_11_71392_931060", "Unmarked parent at depth 11, code 71392",
                "The frontier Boolean is false at remaining fuel 10, original node 931060, the whole prefixCache at depth 11 and code 71392, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17840-929517", "node_context_10_17840_929517", "Original split at fuel 11 and node 929517",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 928893, 929119, 929401, 929516. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71392-931060", "node_context_11_71392_931060", "Original split at fuel 10 and node 931060",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 931001, 931019, 931040, 931059. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17840-929517", "context_10_17840_929517", "Context at depth 10, code 17840, node 929517",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17840 and original node 929517, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_71360_928893, context_11_71361_929119, context_11_71362_929401, context_11_71363_929516.", DescribeRole.Theorem),
            Node("context-12-285572-931082", "context_12_285572_931082", "Context at depth 12, code 285572, node 931082",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 285572 and original node 931082, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
