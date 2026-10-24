using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState;

internal sealed class LiteralsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Literals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire original parent cache and four complete child proposals",
        H("The entire original parent cache and four complete child proposals"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Paragraph(Text("These are data definitions. Their literal values alone prove no update equality, canonical-row invariant, lower inequality or replay acceptance. The Parent, Mirrors, Locals and branch modules supply those distinct proofs.")),
            Node("parentCache", "parentCache", "parentCache",
                "The complete proposed cache for the original depth-eighteen prefix 5335038 retains all sixteen triangle and sixteen singleton State and MirrorRow values. Parent.parent_exact separately proves its equality to the actual original prefixCache.", DescribeRole.Definition),
            Node("childCache0", "childCache0", "childCache0",
                "The complete child-cache proposal for original outcome 0 retains all thirty-two original placements, all State indices and all four fields of every MirrorRow. Its branch step and lower inequality are separate proof obligations.", DescribeRole.Definition),
            Node("childCache1", "childCache1", "childCache1",
                "The complete child-cache proposal for original outcome 1 retains all thirty-two original placements, all State indices and all four fields of every MirrorRow. Its branch step and lower inequality are separate proof obligations.", DescribeRole.Definition),
            Node("childCache2", "childCache2", "childCache2",
                "The complete child-cache proposal for original outcome 2 retains all thirty-two original placements, all State indices and all four fields of every MirrorRow. Its branch step and lower inequality are separate proof obligations.", DescribeRole.Definition),
            Node("childCache3", "childCache3", "childCache3",
                "The complete child-cache proposal for original outcome 3 retains all thirty-two original placements, all State indices and all four fields of every MirrorRow. Its branch step and lower inequality are separate proof obligations.", DescribeRole.Definition),
            Node("nextCache", "nextCache", "nextCache",
                "The four outcomes index childCache0 through childCache3 in their original order. These are complete next-cache proposals; every branch proves its own update equality and lower inequality.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
