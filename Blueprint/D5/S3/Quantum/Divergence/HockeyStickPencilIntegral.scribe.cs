using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class HockeyStickPencilIntegralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/HockeyStickPencilIntegral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted negative inertia of a shifted finite Hermitian pencil is an exact spectral sum.",
        H("The fixed-shift integral in the hockey-stick representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hockey-stick-pencil-weight"),
                DeclarationHandle.Create(Module + ".pencilWeight"),
                H("Pencil weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral")),
                Blocks(Paragraph(Text(
                    "The weight at real t is the reciprocal of the product |t|(t-1)^2. "
                    + "Real inversion assigns zero at t=0 and t=1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integral-weighted-negative-inertia-shifted-pencil"),
                DeclarationHandle.Create(Module + ".integral_weighted_negIndex_shifted_pencil"),
                H("The weighted negative inertia of the actual pencil"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral"),
                    LibraryNoteRef.Create("D5/L/Divergence/hirchetomamichel2024quantum"),
                    LibraryNoteRef.Create("D5/L/Divergence/jencova2024recoverability"),
                    LibraryNoteRef.Create("D5/L/Divergence/liuhirchecheng2025layercake"),
                    LibraryNoteRef.Create("D5/L/Divergence/schmitt2026relative")),
                Blocks(Paragraph(Text(
                    "Let A and B be matrices on a finite complex coordinate space "
                    + "and let r be real with X=A+rI and Y=B+rI positive definite. The shifts imply that both A and B are Hermitian. Set R to the "
                    + "inverse of the positive square root of X. The theorem proves integrability "
                    + "on the real line of the pencil weight times the strict negative eigenvalue "
                    + "count of A+t(B-A)+rI. Its integral is the sum of log(1+λ)-λ/(1+λ) over the "
                    + "eigenvalues of R*(B-A)R, where R* is the conjugate transpose of R and equals R. "
                    + "Congruence reduces the count to the number of tests 1+tλ<0 that hold. "
                    + "Positive λ tests give a left tail and negative λ tests give a right tail. "
                    + "Each contribution is computed by the real improper fundamental theorem of "
                    + "calculus. A zero eigenvalue contributes zero.")),
                    Paragraph(Text(
                        "Frenkel's Lemmas 4–5 and Theorem 6 give the shift and affine-pencil "
                        + "representation of relative entropy. Hirche and Tomamichel's Corollary "
                        + "2.3 gives the two-profile form, and Jenčová's Corollary 1 gives the "
                        + "normalized forward finite-interval form. Liu, Hirche and Cheng's §4.1 "
                        + "gives an earlier operator layer-cake proof. Schmitt's Corollary 4.2 "
                        + "gives the unnormalized affine-pencil and forward-profile formulas."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lintegral-weighted-negative-part-pencil"),
                DeclarationHandle.Create(Module + ".lintegral_weighted_negPart_pencil"),
                H("Integration over all positive shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral"),
                    LibraryNoteRef.Create("D5/L/Divergence/liuhirchecheng2025layercake"),
                    LibraryNoteRef.Create("D5/L/Divergence/schmitt2026relative")),
                Blocks(Paragraph(Text(
                    "For finite positive semidefinite A and B, the nonnegative integral "
                    + "of the pencil weight times the negative-part trace equals the "
                    + "integral over positive r of the fixed-shift spectral sum. The "
                    + "finite layer-cake formula expresses the negative-part trace as "
                    + "an integral of strict negative inertia. Ordered eigenvalue "
                    + "continuity gives joint measurability, so Tonelli's theorem "
                    + "exchanges the pencil parameter and the positive shift."))),
                DescribeRole.Theorem))));
}
