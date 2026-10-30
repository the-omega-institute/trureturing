using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier;

internal sealed class EJMOriginalAdaptiveFrontierBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/EJMOriginalAdaptiveFrontierBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assemble an original adaptive split in its actual prefix context",
        H("Assemble an original adaptive split in its actual prefix context"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Node("accepted", "Accepted", "Adaptive acceptance for an exact occurrence",
                "The proposition applies the adaptive semantic frontier checker to the original decoder, cache step and lower bound, original domination predicate and scale. At depth and code it uses fuel twenty-one minus depth and both full prefix objects; the frontier predicate remains a parameter.", DescribeRole.Definition),
            Node("assemble", "assemble", "Recover the parent from all four actual children",
                "For depth below twenty, assume the frontier is false at the exact parent cache and partial assignment, the literal original node is a split at that depth, and every value child is Accepted at depth plus one and code four times the parent code plus the value. These hypotheses imply parent Accepted. The proof identifies both updated prefix objects and positive child fuel.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
