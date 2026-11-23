using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class SpectralTestLeakageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/LocalCompression/SpectralTestLeakage";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/kuroiwa2021signleakage");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sided leakage estimates for finite quantum channels and their signed tests.",
        H("Spectral test leakage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-spectral-projection"),
                DeclarationHandle.Create(Module + ".positiveSpectralProjection"),
                H("Positive spectral projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a Hermitian complex matrix H on a finite index set, the projection P "
                    + "is the spectral function of H that is one on strictly positive eigenvalues "
                    + "and zero elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spectral-test-leakage-asymmetric"),
                DeclarationHandle.Create(Module + ".spectral_test_leakage_asymmetric"),
                H("Separate spectral floors for the two leakage directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let T(X) = ∑ₐ Kₐ X Kₐ* be trace preserving for a finite family of square Kraus "
                    + "matrices. Let H be Hermitian and suppose every eigenvalue is at least g₊ "
                    + "or at most −g₋, with both floors strictly positive. Write P for the positive "
                    + "spectral projection and Q = I − P. Then twice the sum over a of "
                    + "g₊‖QKₐP‖²_F + g₋‖PKₐQ‖²_F is bounded by the full trace norm of H − T(H). "
                    + "Kuroiwa's Lemma 4.6, equations (4.23)–(4.24), gives the sign-leakage trace "
                    + "terms. The two spectral floors lower-bound them separately. The trace-zero "
                    + "effect inequality contributes the factor of two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-test-leakage"),
                DeclarationHandle.Create(Module + ".spectral_test_leakage"),
                H("Commutator bound for a common spectral floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a trace-preserving finite square Kraus action and a Hermitian H with "
                    + "all eigenvalues at least g or at most −g for g > 0, the positive "
                    + "spectral projection P satisfies 2g∑ₐ ‖PKₐ − KₐP‖²_F ≤ ‖H − T(H)‖₁. "
                    + "The two off-diagonal blocks are orthogonal in the unnormalized "
                    + "Hilbert–Schmidt pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-test-commutator-bound"),
                DeclarationHandle.Create(Module + ".finite_test_commutator_bound"),
                H("Total commutator for finitely many signed tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite family of Hermitian tests Hⱼ = ρⱼ − tⱼσ, take tⱼ and wⱼ "
                    + "nonnegative and assume every eigenvalue of Hⱼ is at least gⱼ or at most "
                    + "−gⱼ for gⱼ > 0. Let Pⱼ be the positive spectral projection of Hⱼ. "
                    + "If δ bounds the full trace-norm reconstruction errors of every ρⱼ "
                    + "and of σ under the trace-preserving finite square Kraus action T, then "
                    + "∑ⱼ wⱼ ∑ₐ ‖[Pⱼ,Kₐ]‖²_F ≤ δ∑ⱼ wⱼ(1+tⱼ)/(2gⱼ). "
                    + "Linearity and the triangle inequality give the factor 1+tⱼ. In the "
                    + "dimension converse, a Hilbert–Schmidt commutator gap γ bounds the squared "
                    + "distance of each Kₐ from the common commutant by its weighted commutator "
                    + "sum divided by γ. The finite-test estimate supplies the numerator of that "
                    + "distance bound. The memory dimension and environment packing argument "
                    + "belongs to the manuscript."))),
                DescribeRole.Theorem))));
}
