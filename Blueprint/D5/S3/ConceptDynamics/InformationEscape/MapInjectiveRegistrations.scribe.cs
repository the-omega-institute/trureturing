using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MapInjectiveRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three frozen maps share one exact injectivity registration template.",
        H("MapInjectiveRegistrations"),
        Blocks(
            Node("markerArena", "The state and output are Fin 2, giving finite coordinates for the two source markers.", DescribeRole.Definition),
            Node("markerRealization", "The identity readout on Fin 2 uses the enrolled mapInjectiveRealization template with instDecidableEqFin 2.", DescribeRole.Definition),
            Node("marker_bridge", "The bridge retains Function.Injective markerDigit verbatim. Local encode and decode maps follow the original digits and constructor order; inverse identities and equality of encoded values transport injectivity in both directions.", DescribeRole.Theorem),
            Node("marker_lawSensitive", "The frozen injectivity theorem satisfies the law through the bridge; a constant readout identifies finite coordinates zero and one.", DescribeRole.Theorem),
            Node("marker_slotSensitive", "The generic sensitivity theorem checks the identity CUT slot on Fin 2.", DescribeRole.Theorem),
            Node("opcodeArena", "The state and output are Fin 12, giving finite coordinates for the twelve source operation codes.", DescribeRole.Definition),
            Node("opcodeRealization", "The identity readout on Fin 12 uses the enrolled mapInjectiveRealization template with instDecidableEqFin 12.", DescribeRole.Definition),
            Node("opcode_bridge", "The bridge retains Function.Injective opcodeIndex verbatim. Local encode and decode maps follow the original indices and constructor order; inverse identities and equality of encoded values transport injectivity in both directions.", DescribeRole.Theorem),
            Node("opcode_lawSensitive", "The frozen injectivity theorem satisfies the law through the bridge; a constant readout identifies finite coordinates zero and one.", DescribeRole.Theorem),
            Node("opcode_slotSensitive", "The generic sensitivity theorem checks the identity CUT slot on Fin 12.", DescribeRole.Theorem),
            Node("rayArena", "The source state is one of the eighteen ray labels, with output in Fin 81.", DescribeRole.Definition),
            Node("rayRealization", "The readout shifts the four ksVectors coordinates by one and packs them as four ternary digits in Fin 81.", DescribeRole.Definition),
            Node("ray_bridge", "The bridge retains Function.Injective ksVectors verbatim.", DescribeRole.Theorem),
            Node("ray_lawSensitive", "The frozen injectivity theorem satisfies the law; the constant zeroth ray code identifies ray labels zero and one.", DescribeRole.Theorem),
            Node("ray_slotSensitive", "The generic sensitivity theorem checks the encoded ray CUT slot.", DescribeRole.Theorem))));

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
