using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0599Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0599.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0599",
        H("Original frontier context coverage 0599"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28756", "selected_cut_28756", "Selected cut at depth 13, code 371830, node 725037",
                "At remaining fuel 8 and original index 725037, selection on the full partial prefix of depth 13 and code 371830 returns the complete row with depth 13, base-four code 371830, original node 725037, kind 2, reserved field 0, 1353 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28802", "selected_cut_28802", "Selected cut at depth 13, code 371903, node 726338",
                "At remaining fuel 8 and original index 726338, selection on the full partial prefix of depth 13 and code 371903 returns the complete row with depth 13, base-four code 371903, original node 726338, kind 2, reserved field 0, 1005 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92957-725043", "unmarked_context_12_92957_725043", "Unmarked parent at depth 12, code 92957",
                "The frontier Boolean is false at remaining fuel 9, original node 725043, the whole prefixCache at depth 12 and code 92957, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-5810-726341", "unmarked_context_10_5810_726341", "Unmarked parent at depth 10, code 5810",
                "The frontier Boolean is false at remaining fuel 11, original node 726341, the whole prefixCache at depth 10 and code 5810, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92957-725043", "node_context_12_92957_725043", "Original split at fuel 9 and node 725043",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 725001, 725021, 725037, 725042. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-5810-726341", "node_context_10_5810_726341", "Original split at fuel 11 and node 726341",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 725573, 725861, 726084, 726340. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-371830-725037", "context_13_371830_725037", "Context at depth 13, code 371830, node 725037",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 371830 and original node 725037, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-5810-726341", "context_10_5810_726341", "Context at depth 10, code 5810, node 726341",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 5810 and original node 726341, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_23240_725573, context_11_23241_725861, context_11_23242_726084, context_11_23243_726340.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
