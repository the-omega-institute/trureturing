using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class GoldenCubicBlockOrbitIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Horizontal cubic rotations isolate coefficients in Mordell point relations.",
        H("Mordell Cubic Orbit Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-orbit-coefficients"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_orbit_independent_mod_fixed"),
                H("Cubic orbit coefficient elimination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Independent coordinate actions and the cubic trace reduce a base-field relation to a positive quadratic norm annihilating one non-torsion point; both integer coefficients vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-family-independent"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence.cubic_mordell_family_independent_mod_base"),
                H("Cubic orbit independence modulo base points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Mordell curve carrying non-torsion points on independently rotated cubic coordinates, each original point and its cubic rotation are independent modulo the base-field point group. The proof uses the horizontal three-point relation and an integral quadratic norm."))),
                DescribeRole.Theorem))));
}
