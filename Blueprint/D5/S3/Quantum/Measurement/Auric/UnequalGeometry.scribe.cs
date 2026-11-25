using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact physical gain range",
        H("The exact physical gain range"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unequal-geometry-statement"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalGeometry.unequal_geometry_statement"),
                H("Range equality in the two working dimensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/lipoon2003principalsubmatrices"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/massey2010noncommutativeschurhorn")),
                Blocks(
                    Paragraph(Text("Fix r between one and the ambient dimension. In the direct branch take working dimension r and traces r q_j. In the complementary branch take corank and traces m_j − r q_j. The gain values on the fiber-flat density inputs are precisely the scaled spectral values of positive effects with identity sum, those traces and ranks at most m_j.")),
                    Paragraph(Text("A state frame supplies one inclusion. Stacking flat factors of the given triple realizes the reverse inclusion, with every effect retained. Division by the original rank r is common to both branches."))),
                DescribeRole.Theorem))));
}
