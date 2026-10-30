using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0775Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0775.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0775",
        H("Original frontier context coverage 0775"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37203", "selected_cut_37203", "Selected cut at depth 13, code 1198107, node 993865",
                "At remaining fuel 8 and original index 993865, selection on the full partial prefix of depth 13 and code 1198107 returns the complete row with depth 13, base-four code 1198107, original node 993865, kind 2, reserved field 0, 637 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37250", "selected_cut_37250", "Selected cut at depth 13, code 1198175, node 995074",
                "At remaining fuel 8 and original index 995074, selection on the full partial prefix of depth 13 and code 1198175 returns the complete row with depth 13, base-four code 1198175, original node 995074, kind 2, reserved field 0, 525 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-299526-993866", "unmarked_context_12_299526_993866", "Unmarked parent at depth 12, code 299526",
                "The frontier Boolean is false at remaining fuel 9, original node 993866, the whole prefixCache at depth 12 and code 299526, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-299543-995075", "unmarked_context_12_299543_995075", "Unmarked parent at depth 12, code 299543",
                "The frontier Boolean is false at remaining fuel 9, original node 995075, the whole prefixCache at depth 12 and code 299543, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-299526-993866", "node_context_12_299526_993866", "Original split at fuel 9 and node 993866",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 993818, 993838, 993857, 993865. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-299543-995075", "node_context_12_299543_995075", "Original split at fuel 9 and node 995075",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 995036, 995050, 995069, 995074. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1198107-993865", "context_13_1198107_993865", "Context at depth 13, code 1198107, node 993865",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1198107 and original node 993865, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-299543-995075", "context_12_299543_995075", "Context at depth 12, code 299543, node 995075",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 299543 and original node 995075, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_1198172_995036, context_13_1198173_995050, context_13_1198174_995069, context_13_1198175_995074.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
