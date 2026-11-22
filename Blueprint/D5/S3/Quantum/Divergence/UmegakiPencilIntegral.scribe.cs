using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiPencilIntegralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/UmegakiPencilIntegral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted negative-part pencil integral gives the corrected finite Umegaki pairing.",
        H("The finite Umegaki pencil integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lintegral-weighted-negative-part-pencil-eq-umegaki"),
                DeclarationHandle.Create(Module + ".lintegral_weighted_negPart_pencil_eq_umegaki"),
                H("Frenkel’s formula for a positive definite reference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral"),
                    LibraryNoteRef.Create("D5/L/Divergence/hirchetomamichel2024quantum"),
                    LibraryNoteRef.Create("D5/L/Divergence/jencova2024recoverability"),
                    LibraryNoteRef.Create("D5/L/Divergence/liuhirchecheng2025layercake"),
                    LibraryNoteRef.Create("D5/L/Divergence/schmitt2026relative")),
                Blocks(
                    Paragraph(Text(
                        "Let A be positive semidefinite and B positive definite on a finite complex "
                        + "coordinate space, including the empty space. Integrate the trace of the "
                        + "negative part of A+t(B−A) over all real t with respect to Lebesgue measure. "
                        + "The weight is 1/(|t|(t−1)²), assigned zero at t=0 and t=1. The nonnegative "
                        + "integral is finite and equals the real trace of A(log A−log B) minus "
                        + "the real trace of A−B, embedded into the nonnegative extended reals.")),
                    Paragraph(Text(
                        "In the original two eigenbases the squared overlaps sum to one along "
                        + "each row and column. For eigenvalues a≥0 and b>0, the primitive "
                        + "(a+r)log((a+r)/(b+r)) tends to a log a−a log b at zero, with a log a "
                        + "equal to zero when a=0. Bounds obtained from the logarithm inequality "
                        + "on the quotient and its reciprocal give the limit a−b at infinity. "
                        + "Integrating the nonnegative negative derivative over r>0 and summing "
                        + "with the overlaps yields the corrected trace pairing.")),
                    Paragraph(Text(
                        "Congruence by the inverse square root of A+rI transforms B+rI into "
                        + "I+K. The determinant identity gives the difference of traces of logs, "
                        + "and trace cyclicity gives the inverse contribution. Functional calculus "
                        + "in K's eigenbasis identifies their sum with the integrand of "
                        + "HockeyStickPencilIntegral.lintegral_weighted_negPart_pencil.")),
                    Paragraph(Text(
                        "The affine-pencil formula is Frenkel’s Theorem 6. Hirche and Tomamichel "
                        + "give the two-profile form in Corollary 2.3 and Eq. (2.22). Jenčová’s "
                        + "Corollary 1 gives the normalized forward finite-interval form, and "
                        + "Schmitt’s Corollary 4.2 treats the unnormalized forms. Liu, Hirche and "
                        + "Cheng give an operator layer-cake proof in §4.1. The identity supplies "
                        + "an analytic input to the separate Fibonacci curve argument."))),
                DescribeRole.Theorem))));
}
