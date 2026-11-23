using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SingleCoordinatePinchingEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equal-trace shifted determinant identity and the entropy cost of pinching one coordinate.",
        H("Shifted determinants and one-coordinate trace entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-log-det-shift-sub"),
                DeclarationHandle.Create(Module + ".integral_log_det_shift_sub"),
                H("Equal-trace shifted determinant integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral")),
                Blocks(Paragraph(Text(
                    "For finite positive semidefinite complex matrices X and Y on the same coordinate "
                    + "space with equal trace, the difference log det(Y + sI) − log det(X + sI) "
                    + "is integrable on s > 0. Its integral is the real trace of X log X minus "
                    + "the real trace of Y log Y. Zero eigenvalues are allowed.")),
                    Paragraph(Text(
                        "Sum the scalar shift kernel of UmegakiPencilIntegral in each spectrum with "
                        + "reference b = 1. The log(1 + s) terms cancel by equal dimension. The "
                        + "terms proportional to 1/(1 + s) and their integrated affine corrections "
                        + "cancel by equal trace. The shifted trace-log identity identifies the "
                        + "remaining spectral sums with the log determinants. The unshifted sums "
                        + "are the actual trace pairings by trace_self_cfc."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-entropy-pinching-bound"),
                DeclarationHandle.Create(Module + ".trace_entropy_pinching_bound"),
                H("Quantitative one-coordinate pinching bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement"),
                    LibraryNoteRef.Create("D5/L/Divergence/frenkel2023integral")),
                Blocks(Paragraph(Text(
                    "Let A have retained block F, coupling column h, and last entry a. Let A₀ "
                    + "retain both diagonal blocks and set the two coupling blocks to zero. "
                    + "Suppose u(C ⊕ λ) ≤ A ≤ v(C ⊕ λ) in the Löwner order, where C is positive "
                    + "definite, C ≤ cI, 0 < λ < c, and 0 < d = (v − u)/2 < u. Then the real "
                    + "trace of A log A minus the real trace of A₀ log A₀ lies between zero and "
                    + "[u d²/(u² − d²)] λ [c/(c − λ)] log(c/λ).")),
                    Paragraph(Text(
                        "The pinching preserves trace. Apply the equal-trace determinant integral "
                        + "and integrate the pointwise Schur bounds. Partial fractions express the "
                        + "upper function as [u d²/(u² − d²)] λ [c/(c − λ)] times the difference "
                        + "1/(s + uλ) − 1/(s + uc). UniformIntegrals.reciprocal_difference "
                        + "evaluates this last integral to log(c/λ).")),
                    Paragraph(Text(
                        "In Fibonacci observation entropy, proof.txt §18 gives u = 4/3 and v = 7/3. "
                        + "Then d = 1/2 and u d²/(u² − d²) = 12/55. For c ≥ 3λ, the factor "
                        + "c/(c − λ) is at most 3/2, giving (18/55) λ log(c/λ). "
                        + "Section 20 uses this same estimate for every ladder length L ≥ 4."))),
                DescribeRole.Theorem))));
}
