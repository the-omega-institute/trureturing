using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2ProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complex-linear projection for the lattice sign involution.",
        H("Projection Onto the Actual Fixed Space"),
        Blocks(
            Paragraph(Text("The lattice data consist of a natural-number rank and a symmetric integral Gram "
                + "matrix with even diagonal. The actual complex carrier consists of finitely supported "
                + "charge families of oscillator polynomials.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-projection"),
                DeclarationHandle.Create(Prefix + "plusProjection"),
                H("Linear projection onto the fixed carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex-linear map from the actual carrier to the fixed carrier "
                    + "sends a state v to (v + theta(v)) / 2, the existing plusPart of the sign involution "
                    + "theta. Applying theta twice gives v, so the average is fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-projection-fixed"),
                DeclarationHandle.Create(Prefix + "plusProjection_fixed"),
                H("Evaluation on a fixed state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Projecting the underlying state of any element of the fixed carrier "
                    + "returns that element of the fixed carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-projection-odd"),
                DeclarationHandle.Create(Prefix + "plusProjection_odd"),
                H("Evaluation on an anti-invariant state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If theta(v) = -v, then the projection of v is zero in the fixed carrier."))),
                DescribeRole.Theorem))));
}
