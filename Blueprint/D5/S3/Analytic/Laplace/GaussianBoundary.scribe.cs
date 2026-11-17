using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class GaussianBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/GaussianBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian averages and the boundary of a paired Laplace transform.",
        H("Gaussian boundary formula"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-boundary"),
                DeclarationHandle.Create(Prefix + "gaussian_boundary"),
                H("Cancellation of the Gaussian spectral sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a positive locally finite spectrum have counting function "
                    + "asymptotic to T log(T)/(2 pi). Let f be measurable and bounded "
                    + "on every interval [0,A] with A>=0. Assume its Laplace integral "
                    + "converges absolutely for every Re(s)>1/2, and, on the strip "
                    + "1/2<Re(s)<1, equals minus one half of the multiplicity-weighted "
                    + "paired pole series plus J. Assume there is 0<eta<1/5 such "
                    + "that J is holomorphic for -eta<Re(s)<1 and has quadratic "
                    + "growth for abs(Re(s))<=eta/2. In addition, assume J is "
                    + "holomorphic for -1/5<Re(s)<1 and "
                    + "has quadratic growth in the imaginary direction on the closed "
                    + "strip from -1/6 to 3/4. There is a positive constant C such "
                    + "that, for M and y at least one, the positive-ray Gaussian "
                    + "average of f is absolutely integrable, and its sum with the "
                    + "Gaussian-weighted cosine spectrum has absolute value at most "
                    + "C M cubed exp(-y/6). Absolute Fubini on Re(s)=3/4 gives "
                    + "Gaussian inversion. Shifting J to Re(s)=-1/6 bounds its "
                    + "contribution. A common quadratic majorant permits passage "
                    + "from finite pole cutoffs to the infinite expansion, while "
                    + "the inverse-square spectral mass bounds the reflected "
                    + "negative-ray corrections."))),
                DescribeRole.Theorem))));
}
