using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoForwardGeodesicBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");
    private static readonly LibraryNoteRef ConditionalEntropy =
        LibraryNoteRef.Create("D5/L/Divergence/bluhm2023continuity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unsmoothed three-qubit witness has geodesic relative entropy log 2 against its faithful reference for every 0 < t ≤ 1.",
        H("Evaluation at the projection boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-geodesic-boundary-geodesicrelativeentropy-of-whitened-projection"),
                DeclarationHandle.Create(Prefix + "geodesicRelativeEntropy_of_whitened_projection"),
                H("Spectral evaluation with a whitened projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "When the first matrix is a positive multiple of a Hermitian projection and whitening gives twice a Hermitian projection Q, the proof uses the stipulated square-root and inverse identities to express the entropy as 2 log 2 times the real trace of the reference times Q. At t = 1 the left spectral factor is the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-boundary-geodesicrelativeentropy-rmatrix-zero"),
                DeclarationHandle.Create(Prefix + "geodesicRelativeEntropy_RMatrix_zero"),
                H("Exact log 2 boundary value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, ConditionalEntropy),
                Blocks(Paragraph(Text(
                    "The unsmoothed matrix is one quarter of a projection. Whitening by the faithful S_u gives I + X_A Z_B Z_C, twice a projection with reference weight one half. The resulting value is log 2 for 0 < u < 1/2 and 0 < t ≤ 1. Lemma 10.14, equation (593), gives the earlier rank-one block mechanism. Proposition 6.7 supplies the Belavkin–Staszewski conditional-entropy antecedent."))),
                DescribeRole.Theorem)),
        []));
}
