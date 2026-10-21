using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037;

internal sealed class ParentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Parent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole original prefix-cache equality for prefix 5335037",
        H("Whole original prefix-cache equality for prefix 5335037"),
        Blocks(
            Paragraph(Text("Each Describe belongs to the actual source module and an existing named public declaration. The original Lean namespace, imports, options, statements and proofs are retained. Private receipts and private helpers receive no public wrappers.")),
            Paragraph(Text("This module belongs to the complete original context at depth eighteen, base-four prefix 5335037, node 442 and remaining fuel three. Its own parent cache, four children and partial assignment remain separate from the other prefixes reaching the same node.")),
            Paragraph(Text("At depth seventeen, prefix 1333759 and node 1305, this context is original outcome 1. Its complete accepted theorem supplies that ordered child to Raw002Tail442/Assembly.raw_cut_00337, which assembles the original context at depth thirteen, prefix 5209 and node 17413 together with every other original sibling along the four preceding outcome-three splits.")),
            Paragraph(Text("Complete-context acceptance retains this prefix's full prefix-cache equality, all four whole-cache steps, all four lower inequalities and original partial assignment. Shared node 442 fixes the replay node only. Reusing an opaque canonical row supplies its indexed full-row equality; the remaining State, cache and prefix-context obligations are earned separately for this prefix.")),
            Node("parent-exact", "parent_exact", "Exact whole prefix-cache equality",
                "The entire parentCache equals EJMOriginalReplayAssembly.prefixCache 18 5335037. The private checkFullCache receipt covers the complete State and all four MirrorRow fields at every original placement; cache_eq_of_checked assembles the equality used by this prefix's accepted theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
