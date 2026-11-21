using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoReverseGeodesicCMICovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A change of basis transports the reverse counterexample to any faithful qubit reference.",
        H("Reverse geodesic CMI for a faithful qubit reference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmicovariance-geodesicrelativeentropy-conjugation"),
                DeclarationHandle.Create(Prefix + "geodesicRelativeEntropy_conjugation"),
                H("Unitary covariance of geodesic relative entropy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Simultaneous conjugation of the two matrices induces a unitary conjugation on matrix-unit coordinates and transports the square-root vector. This is the spectral-form realization of the covariance in Proposition 4.3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmicovariance-reversecmi-conjugation"),
                DeclarationHandle.Create(Prefix + "reverseCMI_conjugation"),
                H("Covariance of the reverse deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The local unitary on C acts on the reference as well as on the state. The actual partial traces conjugate with the retained local unitaries, so both divergences in equation (357) are preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmicovariance-native-result"),
                DeclarationHandle.Create(Prefix + "native_result"),
                H("No modulus on one transported fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Diagonalize the faithful qubit reference and transport the faithful parity witnesses back to the original coordinates. The trace distance and both divergences are preserved. The AB marginal is unchanged by the C rotation, and the rotated AC and BC marginals stay fixed throughout the fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmicovariance-nodimensiononlymodulus"),
                DeclarationHandle.Create(Prefix + "noDimensionOnlyModulus"),
                H("No reverse modulus for faithful three-qubit states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A modulus on all faithful three-qubit states would restrict to the transported fiber, even if it were allowed to depend on the parameter and the faithful reference. This applies throughout the preprint's parameter interval. The binary calculation in equation (384) supplies the earlier implication for the dimension-only question."))),
                DescribeRole.Theorem)),
        []));
}
