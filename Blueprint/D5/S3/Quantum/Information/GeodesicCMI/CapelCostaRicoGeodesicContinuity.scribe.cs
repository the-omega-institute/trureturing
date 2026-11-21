using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoGeodesicContinuityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed second matrix, geodesic relative entropy is continuous in the first matrix on the positive semidefinite cone.",
        H("Continuity at fixed reference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geodesic-continuity-geodesicmodular-possemidef"),
                DeclarationHandle.Create(Prefix + "geodesicModular_posSemidef"),
                H("Positivity of the modular matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A positive semidefinite first matrix gives positive semidefinite powers. The inverse square root of the second matrix is self-adjoint in the real continuous functional calculus, and congruence preserves positivity of the right factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geodesic-continuity-continuouson-geodesicmodular"),
                DeclarationHandle.Create(Prefix + "continuousOn_geodesicModular"),
                H("Continuity of the modular matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For 0 ≤ t ≤ 1, the two matrix powers vary continuously on the positive semidefinite cone. At t = 1 the left power is the identity, including at singular first matrices. The second matrix is fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geodesic-continuity-continuouson-geodesicrelativeentropy"),
                DeclarationHandle.Create(Prefix + "continuousOn_geodesicRelativeEntropy"),
                H("Continuity of the spectral quadratic form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Continuity of z log z at zero gives continuity after applying the spectral function to the modular matrix. Pairing with the fixed reference vector proves first-argument continuity for each 0 ≤ t ≤ 1. The forward construction uses this theorem with a faithful reference held fixed during each regularization."))),
                DescribeRole.Theorem)),
        []));
}
