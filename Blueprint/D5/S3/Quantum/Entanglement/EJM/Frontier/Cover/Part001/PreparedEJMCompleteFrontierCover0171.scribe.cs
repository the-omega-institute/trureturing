using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0171Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0171.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0171",
        H("Original frontier context coverage 0171"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08211", "selected_cut_08211", "Selected cut at depth 13, code 91443, node 231808",
                "At remaining fuel 8 and original index 231808, selection on the full partial prefix of depth 13 and code 91443 returns the complete row with depth 13, base-four code 91443, original node 231808, kind 2, reserved field 0, 1169 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08258", "selected_cut_08258", "Selected cut at depth 13, code 91499, node 232464",
                "At remaining fuel 8 and original index 232464, selection on the full partial prefix of depth 13 and code 91499 returns the complete row with depth 13, base-four code 91499, original node 232464, kind 2, reserved field 0, 1001 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22860-231809", "unmarked_context_12_22860_231809", "Unmarked parent at depth 12, code 22860",
                "The frontier Boolean is false at remaining fuel 9, original node 231809, the whole prefixCache at depth 12 and code 22860, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22874-232465", "unmarked_context_12_22874_232465", "Unmarked parent at depth 12, code 22874",
                "The frontier Boolean is false at remaining fuel 9, original node 232465, the whole prefixCache at depth 12 and code 22874, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22860-231809", "node_context_12_22860_231809", "Original split at fuel 9 and node 231809",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 231781, 231800, 231808. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22874-232465", "node_context_12_22874_232465", "Original split at fuel 9 and node 232465",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 232425, 232455, 232464. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-91443-231808", "context_13_91443_231808", "Context at depth 13, code 91443, node 231808",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91443 and original node 231808, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-22874-232465", "context_12_22874_232465", "Context at depth 12, code 22874, node 232465",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22874 and original node 232465, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_91496_3444, context_13_91497_232425, context_13_91498_232455, context_13_91499_232464.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
