using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class QutritDiagonalResetOptimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");

    private const string Owner = "D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalResetOptimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pure qutrit Bell-source trace-distance minimum for diagonal-reset compression through a qubit.",
        H("Exact optimum for pure diagonal-reset qutrit compression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qutrit-stationary-characteristic"),
                DeclarationHandle.Create(Owner + "exists_stationary_characteristic"),
                H("An exact rational bracket for the stationary amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "The accompanying isotropic-compression manuscript supplies the stationary "
                    + "characteristic-polynomial certificate. Solve the stationarity equation for "
                    + "the spectral parameter and substitute the resulting rational function into "
                    + "the characteristic polynomial. Its denominator is negative throughout "
                    + "the closed interval with endpoints 0.80680296 and 0.80680298. Exact "
                    + "rational signs at the endpoints give an interior zero by continuity. At "
                    + "the resulting spectral parameter, the quartic Taylor identity gives a "
                    + "strictly negative determinant at every other amplitude in [0, 1]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-pure-diagonal-reset-optimum"),
                DeclarationHandle.Create(Owner + "pure_diagonal_reset_optimum"),
                H("The pure reset and two-Kraus decoder attain the minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "The first two pivots of the shifted matched block are positive at the "
                    + "stationary root, and its residual Schur complement vanishes. The resulting "
                    + "positive semidefinite form bounds every unit-vector expectation. A strictly "
                    + "larger shift than the greatest expectation would be positive definite and "
                    + "would have positive determinant. At every other amplitude the negative "
                    + "determinant instead forces a strictly larger Rayleigh maximum. The retained "
                    + "Rayleigh attainment theorem and diagonal-reset converse transfer these "
                    + "comparisons to half the joint trace norm. The strict comparison identifies "
                    + "the unique attenuation amplitude within the explicit family. The channel "
                    + "comparison quantifies over plane-preserving diagonal resets and arbitrary "
                    + "qubit-to-qutrit decoders at the pure endpoint."))),
                DescribeRole.Theorem))));
}
