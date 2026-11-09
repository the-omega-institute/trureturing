using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class PairedLaplaceWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/PairedLaplaceWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square mass of paired Laplace data on logarithmic windows.",
        H("Gaussian transfer to the original function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-laplace-window-lower"),
                DeclarationHandle.Create(Prefix + "paired_laplace_window_lower"),
                H("A window mean-square lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a positive ordinate spectrum have the counting asymptotic "
                    + "N(T)/(T log T) tending to 1/(2 pi), a logarithmic local count, "
                    + "and the averaged Montgomery lower bound. Suppose f has paired "
                    + "Laplace data with quadratic growth, and its regular part is "
                    + "holomorphic and polynomially bounded on the wider Gaussian strip. "
                    + "There is c>0 such that, for all sufficiently large M, the integral "
                    + "of f(y) squared from 16 log M minus two to 20 log M plus two "
                    + "is at least c M (log M) squared. The Gaussian boundary formula "
                    + "compares the Gaussian average with the cosine spectrum. Initial "
                    + "Laplace convergence at three quarters bounds the discarded "
                    + "Gaussian tails after truncating f to the larger window. Young's "
                    + "inequality transfers the remaining square mass to f."))),
                DescribeRole.Theorem))));
}
