using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class DiamondClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum on the diamond closure",
        H("Minimum on the diamond closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-distance-to-protocol-closure"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DiamondClosure.exact_distance_to_protocol_closure"),
            H("Minimum on the diamond closure"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The same normalized purification bounds every channel approximated in diamond norm by finite randomized trees. The explicit finite simulator attains the minimum."))),
            DescribeRole.Theorem))));
}
