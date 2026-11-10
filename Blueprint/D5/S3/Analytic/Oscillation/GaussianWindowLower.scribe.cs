using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class GaussianWindowLowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/GaussianWindowLower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian spectral sums inherit logarithmic window mass from hard cutoffs.",
        H("Gaussian window lower bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-window-lower"),
                DeclarationHandle.Create(Prefix + "gaussian_window_lower"),
                H("Transferring spectral window mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let S be a positive locally finite spectrum with positive integer multiplicities. "
                    + "Assume N(T)/(T log T) tends to 1/(2 pi), the multiplicity in each unit "
                    + "interval is bounded by a constant times log(T+3), and the averaged Montgomery "
                    + "lower bound holds. There is c>0 such that, for every sufficiently large M, "
                    + "the integral of the squared Gaussian cosine sum over "
                    + "[16 log M-1,20 log M+1] is at least c M (log M)². "
                    + "A smooth cutoff of width M^(1/4) cancels the Gaussian weights below M. "
                    + "Absolute convergence permits convolution term by term. The transition band "
                    + "contributes at most a constant times M^(1/4) log(2+M). Truncating the Gaussian "
                    + "sum to the enlarged interval adds at most a constant times log(2+M) on the "
                    + "inner interval, because the cutoff kernel has integral tail of order 1/M. "
                    + "The combined squared error is negligible compared with M (log M)². "
                    + "The Fourier multiplier bound exp(2) then transfers the hard-cutoff lower "
                    + "bound to the Gaussian sum."))),
                DescribeRole.Theorem))));
}
