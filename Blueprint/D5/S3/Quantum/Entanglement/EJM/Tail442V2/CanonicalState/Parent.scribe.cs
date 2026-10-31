using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState;

internal sealed class ParentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Parent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full literal cache equals the actual original prefix cache",
        H("The full literal cache equals the actual original prefix cache"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Node("parent-exact", "parent_exact", "Exact whole prefix-cache equality",
                "The complete parentCache equals EJMOriginalReplayAssembly.prefixCache 18 5335038. The private checkFullCache receipt covers every State and all four MirrorRow fields at every original triangle and singleton placement; cache_eq_of_checked assembles the whole equality. Accepted consumes this equality to bind the literal tail to its actual original prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
