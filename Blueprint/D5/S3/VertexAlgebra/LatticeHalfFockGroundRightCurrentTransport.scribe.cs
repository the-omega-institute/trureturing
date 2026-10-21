using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockGroundRightCurrentTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ground-first native right-current transport on the distinct source and actual tensor carriers.",
        H("Ground-first native right-current transport"),
        Blocks(
            Paragraph(Text("The module retains both projected charged ground components, the source zero mode, signed physical lifts and the actual tensor current. It proves the simple-pole Ward collapse and a finite ordered eight-composition cancellation on the original tensor carrier.")),
            Describe.Lean(
                DescribeId.Create("ground-right-current-positive-neutral"),
                DeclarationHandle.Create(Prefix + "projectedGround_positive_neutral"),
                H("Positive source currents vanish on both projected ground components"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two Bool-named projected signs are retained; every positive source neutral mode vanishes by the literal polynomial derivative formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-current-ward"),
                DeclarationHandle.Create(Prefix + "projectedGround_current_ward"),
                H("Ground Ward collapse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native Ward sum collapses to the source zero-mode output slice with its signed lift increment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-current-finite-transport"),
                DeclarationHandle.Create(Prefix + "ground_finite_right_transport"),
                H("Finite ground right-current cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite ordered compositions cancel pairwise; the two surviving commutators are exactly the explicit finite correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ground-right-current-native-consumer"),
                DeclarationHandle.Create(Prefix + "projectedGround_finite_right_transport"),
                H("Native projected-ground consumer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite cancellation is instantiated with correctedField slices and the actual tensor current on arbitrary original target inputs."))),
                DescribeRole.Theorem),
            Paragraph(Text("The finite step leaves the full signed inverse-convolution bridge, the exact projected ground-pair base and arbitrary-first transport open.")))));
}
