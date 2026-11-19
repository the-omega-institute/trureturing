using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class TiltedInstrumentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realization by one projective measurement",
        H("Realization by one projective measurement"),
        Blocks(Describe.Lean(
            DescribeId.Create("realizes-tilted-operators"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/TiltedInstrument.realizes_tilted_operators"),
            H("Realization by one projective measurement"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The tilted branch operators are partial isometries on complementary rank-three and rank-two supports. Their unitary extensions give a legal complete projective protocol."))),
            DescribeRole.Theorem))));
}
