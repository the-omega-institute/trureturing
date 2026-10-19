using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335036;

internal sealed class AcceptedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335036/Accepted.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original complete-context Accepted statement for original prefix 5335036",
        H("Exact original complete-context Accepted statement for original prefix 5335036"),
        Blocks(
            Paragraph(Text("Each Describe belongs to the actual source module and an existing named public declaration. The original Lean namespace, imports, options, statements and proofs are retained. Private receipts and private helpers receive no public wrappers.")),
            Paragraph(Text("This module belongs to the complete original context at depth eighteen, base-four prefix 5335036, node 442 and remaining fuel three. Its own parent cache, four children and partial assignment remain separate from the other prefixes reaching the same node.")),
            Paragraph(Text("At depth seventeen, prefix 1333759 and node 1305, this context is original outcome 0. Its complete accepted theorem supplies that ordered child to Raw002Tail442/Assembly.raw_cut_00337, which assembles the original context at depth thirteen, prefix 5209 and node 17413 together with every other original sibling along the four preceding outcome-three splits.")),
            Paragraph(Text("Complete-context acceptance retains this prefix's full prefix-cache equality, all four whole-cache steps, all four lower inequalities and original partial assignment. Shared node 442 fixes the replay node only. Reusing an opaque canonical row supplies its indexed full-row equality; the remaining State, cache and prefix-context obligations are earned separately for this prefix.")),
            Node("all-steps", "all_steps", "All steps",
                "For all four outcomes, the complete coordinate-eighteen step of this prefix's parentCache equals its matching entire nextCache. Each case consumes that prefix's own branch step.", DescribeRole.Theorem),
            Node("all-bounds", "all_bounds", "All bounds",
                "For every outcome, the original scale is at most lower of this prefix's entire nextCache. The four case proofs use the matching branch inequalities without substituting another prefix's totals.", DescribeRole.Theorem),
            Node("literal-context", "literal_context", "Literal context",
                "The original replay check holds at fuel three, node 442, this prefix's entire literal parentCache and prefixPartial 18 5335036. Helper.tail442 consumes this context's all_steps and all_bounds.", DescribeRole.Theorem),
            Node("accepted", "accepted", "Accepted",
                "The statement is EJMOriginalReplayAssembly.Accepted 18 5335036 at original node 442. Its proof uses this prefix's parent_exact to connect the entire literal cache with the original prefixCache and then uses its literal_context, preserving the original partial assignment.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
