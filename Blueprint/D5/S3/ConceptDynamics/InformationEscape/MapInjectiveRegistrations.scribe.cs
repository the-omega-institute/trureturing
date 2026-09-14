using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MapInjectiveRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three frozen maps share one exact injectivity registration template.",
        H("MapInjectiveRegistrations"),
        Blocks(
            Node("markerFintype", "The local finite enumeration contains exactly the two source markers.", DescribeRole.Definition),
            Node("markerArena", "The source state is a Marker, with natural-number output.", DescribeRole.Definition),
            Node("markerRealization", "The readout is the frozen markerDigit map without reduction by its injectivity proof.", DescribeRole.Definition),
            Node("marker_bridge", "The bridge retains Function.Injective markerDigit verbatim.", DescribeRole.Theorem),
            Node("marker_lawSensitive", "The frozen injectivity theorem satisfies the law; a constant readout identifies the two distinct markers.", DescribeRole.Theorem),
            Node("marker_slotSensitive", "The generic sensitivity theorem checks the marker-digit CUT slot.", DescribeRole.Theorem),
            Node("opcodeFintype", "The local finite enumeration contains exactly the twelve source operation codes.", DescribeRole.Definition),
            Node("opcodeArena", "The source state is an Opcode, with natural-number output.", DescribeRole.Definition),
            Node("opcodeRealization", "The complete opcodeIndex map is the only readout.", DescribeRole.Definition),
            Node("opcode_bridge", "The bridge retains Function.Injective opcodeIndex verbatim.", DescribeRole.Theorem),
            Node("opcode_lawSensitive", "The frozen injectivity theorem satisfies the law; a constant map identifies the distinct gen and enc codes.", DescribeRole.Theorem),
            Node("opcode_slotSensitive", "The generic sensitivity theorem checks the opcode-index CUT slot.", DescribeRole.Theorem),
            Node("rayArena", "The source state is one of the eighteen ray labels, with integer-vector output.", DescribeRole.Definition),
            Node("rayRealization", "The readout is the unchanged ksVectors map into four integer coordinates.", DescribeRole.Definition),
            Node("ray_bridge", "The bridge retains Function.Injective ksVectors verbatim.", DescribeRole.Theorem),
            Node("ray_lawSensitive", "The frozen injectivity theorem satisfies the law; the constant zeroth vector identifies ray labels zero and one.", DescribeRole.Theorem),
            Node("ray_slotSensitive", "The generic sensitivity theorem checks the integer-vector CUT slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
