using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class NonnegativeBoundaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Widder1941 =
        LibraryNoteRef.Create("D5/L/Fourier/widder1941laplace");

    private const string Prefix = "D5/S3/Analytic/Laplace/NonnegativeBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive measure supported on the nonnegative real axis has a singularity at a finite boundary of exponential integrability.",
        H("Nonnegative exponential transforms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integrable-exp-of-holomorphic-extension"),
                DeclarationHandle.Create(Prefix + "integrable_exp_of_holomorphic_extension"),
                H("Holomorphic extension and exponential integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let mu be a measure on the real line supported on the nonnegative axis. "
                    + "Suppose t lies in the interior of the interval where exp(t*x) is integrable. "
                    + "Let F be holomorphic on the complex ball of radius r about t and agree "
                    + "near t with the exponential transform integral exp(z*x) dmu(x). "
                    + "For every h with 0<=h<r, exp((t+h)*x) is integrable. "
                    + "The Taylor coefficients at t are the moments integral x^n*exp(t*x) dmu(x) "
                    + "divided by n factorial. These moments are nonnegative. Taylor convergence "
                    + "at t+h and the monotone interchange of the nonnegative exponential series "
                    + "with integration give the asserted integrability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integrable-exp-on-real-ray"),
                DeclarationHandle.Create(Prefix + "integrable_exp_on_real_ray"),
                H("Continuation along the real ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let mu be a measure supported on the nonnegative real axis and suppose "
                    + "its exponential integral converges at some real parameter. Let U be open "
                    + "and contain every real t<a, and let F be holomorphic on U. Suppose F "
                    + "agrees locally with the defining transform at every t<a in the interior "
                    + "of the interval of exponential integrability. Then exp(t*x) is integrable "
                    + "for every t<a. If one such parameter failed, positivity makes the "
                    + "convergence interval downward closed with finite supremum c<a. A ball "
                    + "about c contained in U and the preceding Taylor argument give integrability "
                    + "strictly to the right of c, a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-exponential-boundary"),
                DeclarationHandle.Create(Prefix + "nonnegative_exponential_boundary"),
                H("A singularity at the convergence boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Widder1941),
                Blocks(Paragraph(Text(
                    "Let mu be a measure on the nonnegative real axis and c a finite real number. "
                    + "Assume exp(t*x) is integrable for every t<c and is not integrable for any t>c. "
                    + "There is no positive radius r and holomorphic F on the ball about c of radius r "
                    + "which agrees with the exponential transform on the part of that ball with Re(z)<c. "
                    + "Indeed choose t=c-r/4. Taylor convergence on the ball about t of radius r/2 "
                    + "implies integrability at t+r/3>c, contradicting the convergence boundary. "
                    + "Replacing z by -s gives the corresponding nonnegative Laplace-transform theorem "
                    + "at its finite abscissa of convergence. "
                    + "This formulation uses a general positive measure, extending Widder's "
                    + "nonnegative locally integrable function formulation."))),
                DescribeRole.Theorem))));
}
