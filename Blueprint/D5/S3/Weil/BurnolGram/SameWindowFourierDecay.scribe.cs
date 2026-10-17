using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.BurnolGram;

internal sealed class SameWindowFourierDecayDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/BurnolGram/SameWindowFourierDecay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual same-window cutoff error has an interior derivative budget and angular Fourier decay with both endpoint jumps paid.",
        H("Fourier decay of the actual same-window error"),
        Blocks(
            Paragraph(Text(
                "Use the actual interior-box convolution cutoff chi and its actual bundled "
                + "Weil test T=chi*p in the original window [-a,a]. Assume h>0, 4h<=a, "
                + "a smooth even complex input p, and bounds |p|<=M, |p'|<=M1 with M,M1>=0 "
                + "on that window. The zero-extension error is E=1_{(-a,a)}p-T; it may jump "
                + "at both endpoints and is not asserted to be a Weil test function.")),
            Describe.Lean(
                DescribeId.Create("actual-interior-derivative-budget"),
                DeclarationHandle.Create(Owner + "sameWindowSmoothTrial_derivative_L1_error_le"),
                H("Only the two boundary strips pay the derivative error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of |(p-T)'| on the closed original window is at most "
                    + "2M+4h*M1. The plateau makes the derivative vanish in the central open "
                    + "interval. Two strips of total length 4h pay the p' term, while the "
                    + "actual cutoff derivative has integral at most two. Integrability of "
                    + "that derivative follows from smoothness and compact support; the "
                    + "bound is not inferred from a totalized non-integrable integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-angular-fourier-error-budget"),
                DeclarationHandle.Create(Owner + "sameWindowSmoothTrial_fourier_error_bounds"),
                H("The actual angular transform pays both endpoint jumps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem establishes Integrable E and, for every real angular "
                    + "frequency t, integrability of exp(-i*t*x)*E(x). Its Fourier integral "
                    + "has norm at most 4M*h for all t and at most (4M+4h*M1)/|t| when "
                    + "t is nonzero. The live interval integration-by-parts identity uses "
                    + "the smooth interior error p-T and retains the traces p(-a), p(a). "
                    + "Their combined norm costs 2M in addition to the proved interior "
                    + "derivative budget. Endpoint values of the open-window zero extension "
                    + "do not erase these traces, and evenness does not cancel them at a "
                    + "general real frequency. The kernel uses angular frequency with no "
                    + "extra 2*pi factor. This module supplies no weighted integral estimate, "
                    + "closed-form comparison, signed negative Weil trial, or RH conclusion."))),
                DescribeRole.Theorem))));
}
