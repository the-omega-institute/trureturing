using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMGlobalDAGDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMGlobalDAGData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal shared split shapes for actual-context EJM global replay.",
        H("Sharing branch data never transfers an arithmetic proof between contexts"),
        Blocks(
            Paragraph(Text("Size is 1646021: one bound tag, 92160 possible symmetry cut tags and 1553860 literal shared split shapes. A split shape stores four 21-bit child references, giving 84 bits per shape and 256 shapes per packed natural number. The indexed node decoder also uses the current fuel to determine the actual split coordinate. Consequently a shared shape is replayed separately in every reached partial assignment; no stored arithmetic proof or minimum is inherited from another context. This data module proves neither global acceptance nor a score margin. The complete actual-context checker, actual lower-bound soundness and earned score/rank symmetry laws must be kernel-checked before the exact certificate consumer obtains its global conclusion.")),
            Node("shape-word", "shapeWord", "Decode the four actual child references of a shared shape",
                "A natural-number shape index selects its packed payload by division by 256 and extracts its 84-bit field by remainder. This is the original total data decoder used by the node interpreter, without a trusted validity theorem."),
            Node("nodes", "nodes", "Interpret an indexed node in its actual fuel context",
                "Index zero is a bound leaf. Indices one through 92160 decode an actual global source/outcome action and stored pivot via cutOfTag. The remaining indices decode four child references into a split at coordinate (21 minus fuel) modulo 20. The original replay starts with fuel 21, so its first split fills coordinate zero. Modular totality and branch-data sharing do not prove any lower bound or strict dominance."),
            Node("root", "root", "The literal original global root index",
                "The root is the final index 1646020 in Fin Size. The proof in this definition only establishes index well-formedness. Acceptance of replay from this root with fuel 21 and the all-unknown partial assignment remains the separate complete kernel computation in the actual exact-certificate consumer."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
