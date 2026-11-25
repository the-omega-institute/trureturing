using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class UnitarySpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum";
    private static readonly LibraryNoteRef Johnston = LibraryNoteRef.Create("D5/L/ProcessReconstruction/johnston2009computing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral chords of a relative unitary and expectations on finite reference extensions.",
        H("Relative Unitary Spectrum"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-chord-bound"),
                DeclarationHandle.Create(Module + ".spectrum_chord_le"),
                H("Doubled operator norm bounds every spectral chord"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Johnston),
                Blocks(Paragraph(Text(
                    "Choose any two spectral points of a finite unitary W. An eigenvector in the "
                    + "tensor product built from eigenvectors for the two points shows that their "
                    + "chord length is bounded by the operator norm of W† ⊗ W minus the identity."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("spectrum-reference"),
                DeclarationHandle.Create(Module + ".reference_spectrum_subset"),
                H("Reference amplification preserves spectral inclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every spectral point of the finite reference amplification of a unitary "
                    + "lies in the original spectrum. Take a nonzero reference component of an "
                    + "eigenvector of the amplified unitary."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("spectral-expectation"),
                DeclarationHandle.Create(Module + ".re_inner_ge_of_spectrum"),
                H("A spectral half-plane bounds every unit-vector expectation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Johnston),
                Blocks(Paragraph(Text(
                    "A common lower bound for the real parts of the rotated spectral points of "
                    + "a unitary bounds the real part of each similarly rotated expectation in a "
                    + "unit vector. The proof uses positivity of the real part after subtracting "
                    + "the scalar threshold."))), DescribeRole.Lemma))));
}
