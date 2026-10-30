using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class ExponentialPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite separation of the entire quadratic weighted Hankel kernel is equivalent to an exponential-polynomial presentation.",
        H("Entire weighted Hankel kernels and exponential polynomials"),
        Blocks(Describe.Lean(DescribeId.Create("entire-weighted-hankel-exponential-polynomial"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/ExponentialPolynomial.finite_weighted_separation_iff_exponential_polynomial"),
            H("Finite separation on the whole complex plane"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The quantifier is every entire complex-valued function on Complex. Finite separation means that some natural k and two families of k entire factors represent (z-w)^2*f(z+w) at every complex pair. An exponential polynomial is a finite sum exp(alpha_i*z)*P_i(z), with arbitrary complex exponents and arbitrary complex polynomial coefficients. Repeated exponents and zero polynomials are allowed in this presentation.")),
                Paragraph(Text("Two applications of the difference of the scalar partial derivatives remove the quadratic weight and produce 8*f(z+w). The complete span of all complex translates of f is then finite dimensional. Its product topology is Hausdorff, and finite dimension makes the subspace closed. Pointwise convergence of actual difference quotients proves that scalar differentiation preserves it. No unbounded differentiation operator on a Fock Hilbert space is introduced.")),
                Paragraph(Text("The resulting actual derivative endomorphism decomposes into generalized eigenspaces over Complex. Multiplication by exp(-alpha*z) turns a generalized derivative eigenvector into an entire function with a vanishing iterated derivative. Polynomial primitives and the zero-derivative constant-function theorem reconstruct a genuine polynomial. Conversely, expanding each polynomial at z+w and splitting each exponential gives finitely many entire separated terms.")),
                Paragraph(Text("The statement is about entire functions and finite pointwise separation. Reconstructing actual Hilbert vectors from a completed kernel, proving factorial summability of every polynomial-exponential block, and identifying the existing physical channel are separate modules. The theorem alone does not classify rank three and proves no entropy inequality or all-input elementary-symmetric lower bound."))),
            DescribeRole.Theorem))));
}
